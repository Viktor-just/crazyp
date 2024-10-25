#!/usr/bin/env perl

# server.pl - an example of AnyEvent alternative for a fully-async server
#  capable of running some blocking commands.
#
# Copyright 2024 Viktor G. (AKA 'Just Viktor', GitHub handle Viktor-just).
#
# Published intellectual property protected by Copyright law in Russia.
# GitHub handle 'Viktor-just' is taken as a pen name in accordance with
#  provisions of Article 1265 of Russian Civil code.
################################################################### 
# This Source Code Form is subject to the terms of the Mozilla Public
#  License, v. 2.0. If a copy of the MPL was not distributed with this
#  file, You can obtain one at https://mozilla.org/MPL/2.0/. 
#
# This Source Code Form is “Incompatible With Secondary Licenses”, as
#  defined by the Mozilla Public License, v. 2.0.
################################################################### 

use warnings;
use strict;
use diagnostics;

use autodie;
use feature qw( switch );
use sigtrap;

use constant PORT_NUMBER => 19_291;     # any free TCP port number would do
use constant BUFSIZE     =>    512;     # bytes
use constant IDLE_TMO    =>     30;     # seconds for new request to appear
use constant WR_STALL_TMO=>      5;     # seconds for response progress
use constant ASYNC_TMO   =>      5;     # seconds, timeout for async cmds.

use Carp qw( :DEFAULT cluck );
use Errno;
use English qw( -no_match_vars );
use Fcntl qw( :DEFAULT :flock );
use File::Basename qw( basename );
use File::Spec;

# TODO: should IO::Select become insufficient (e.g. file descriptors number-wise), try and employ IO::Poll
use IO::Select;

use IO::Socket;
use List::Util qw(first max min);
use MIME::Base64;
use Net::hostent;   # for fancy gethostbyaddr which returns an object
use POSIX qw( :sys_wait_h );
use Scalar::Util qw( refaddr );
use Socket qw( :DEFAULT :crlf );
use Storable qw( freeze thaw );
use Sys::Syslog qw( :DEFAULT :standard :macros );

BEGIN {
    my $tm  = ${^TAINT};
    my $lbn = $ENV{LD_BIND_NOW};
    # For debugging
    carp "Taint mode is @{[ $tm ? 'on' : 'off' ]}";
    carp "LD_BIND_NOW is @{[ $lbn ? q{} : 'not ' ]}set";

    if ( not $tm or not $lbn ) {
        # helps in reducing jitters and speed up fork()s
        $ENV{LD_BIND_NOW} = 1;
        exec $EXECUTABLE_NAME, '-T', $PROGRAM_NAME, @ARGV or kill -9 => $PID;
    }

    # sane PATH for taint mode.
    $ENV{PATH} = '/usr/sbin:/usr/bin:/sbin:/bin:/opt/bin';
}

my $PROMPT = 'Command? ';
my ($HELP, $QUIT, $STATUS, $FORGET, $LIST_BLOCK, $LIST_NETIF, $SHOW_MEM)
    = qw( help quit status forget list_block list_netif show_mem );
my @commands = ($HELP, $QUIT, $STATUS, $FORGET, $LIST_BLOCK,
                $LIST_NETIF, $SHOW_MEM,);
my @help = @commands;

my $RESULT = 'result';
push @commands, $RESULT;

ensure_singleton();
require_root();     # NB, this is for blockdev which sits @ /sbin and requires EUID=0
my ($lsblk, $udevadm, $udevinfo, $blockdev, $free,) =
    find_tools(qw(
     lsblk   udevadm   udevinfo   blockdev   free
    ));

init_logger();
daemonize();
main_loop();

sub require_root { croak 'Must be root' unless $EUID == 0; return; }
sub find_tools {
    my @result;
    foreach my $tool (@_) {
        my $output = `which $tool 2>&1`;
        chomp $output;
        my ( $untainted ) = ($output =~ m/\A (.+) \z/msx);
        push @result, ($CHILD_ERROR ? undef : $untainted);
    }
    return @result;
}

sub main_loop {
    # Based on IO::Socket-based TCP server implementation, shamelessly borrowed from
    # L<perlipc/"TCP Servers with IO::Socket">.
    my $server = IO::Socket::INET->new( Proto     => "tcp",
                                        LocalPort => PORT_NUMBER,
                                        Listen    => SOMAXCONN,
                                        Reuse     => 1,
                                        Blocking  => 0,
                                      );

    croak "can't setup server" unless $server;
    debug("[Server $0 accepting clients]");

    # indexed by client ID, serves as a high-level buffer for response(s)
    my %response;

    $SIG{CHLD} = \&REAPER;
    while (1) {
        forget_stale_async();
        my ($rdr, $wrr, $to_read, $to_write) =
            wait_and_accept_ready_connections({server_socket => $server,
                                               responses => \%response,
                                             });

        foreach my $conn (@{$wrr}) {
            my $contents = delete $response{$conn->get_id()} || [q{}];
            my $written = 0;
            foreach my $line (@{$contents}) {
                $written += $conn->send($line);
            }
            if (not $written) {
                # the socket was claimed as "ready for writing" but
                # did not progress at all. This means the remote shutdown.
                $conn->discard_outgoing_data();
            }
        }
        foreach my $conn (@{$rdr}) {
            my $resp_buf = $response{$conn->get_id()} ||= [];
            my @lines = $conn->recv();
            foreach my $line (@lines) {
                my $text = 
                    handle_protocol({command => $line,
                                     client_connection => $conn,
                                   });

                push @{$resp_buf}, $text if $text;
            }
            if ($conn->is_eof()) {
                $conn->close() if ! $conn->has_more_outgoing_data();
            }
        }

        # handle connections to be terminated.
        my $now = time;
        foreach my $conn (Connection->get_all_connections()) {
            my $s = $conn->get_socket();

            my ($rd_last_ts, $wr_last_ts) = $conn->get_heartbeats();
            my $reason = ($to_read->exists($s)  and $rd_last_ts <= $now - IDLE_TMO)
                       ? "Idle too long"
                       : ($to_write->exists($s) and $wr_last_ts <= $now - WR_STALL_TMO)
                       ? "Write stalled"
                       : q{};
            if ($reason) {
                $conn->send($reason . $CRLF);
                $conn->close();
                delete $response{$conn->get_id()};
            }
        }
    }
    return;
}

sub accept_new {
    my $server = shift;
    # the below connection gets kept in Connection package (think
    # Singleton) and its further lifecycle gets fully managed on
    # subsequent iterations of the caller's loop.
    my $s = $server->accept();
    my $client = Connection->new({socket => $s,
                                  bufsize => BUFSIZE,
                                });

    my $hostinfo = gethostbyaddr($s->peeraddr);
    debug("[Connect from %s]", $hostinfo ? $hostinfo->name : $s->peerhost);

    my $bn = basename $PROGRAM_NAME;
    $client->send("Welcome to $bn; type help for command list.$CRLF");
    $client->send($PROMPT);
    return  $client;
}

sub wait_and_accept_ready_connections {
    my $arg = shift;
    my ($listening_socket, $responses) = @{$arg}{qw(server_socket responses)};

    my $to_write = IO::Select->new();
    my $to_read  = IO::Select->new($listening_socket);
    foreach my $c (Connection->get_all_connections()) {
        my $id = $c->get_id();
        my $s = $c->get_socket();

        my $i_have_data = (exists $responses->{$id} and @{$responses->{$id}});
           $i_have_data ||= $c->has_more_outgoing_data();
        $to_write->add($s) if $i_have_data;

        if ($c->is_eof()) {
            # don't keep sockets that cannot change at all,
            $c->close() if ! $to_write->exists($s);
            next;
        }
        $to_read->add($s);
    }

    my $tmo = my $inf = 9**9**9;
    my $now = time;
    foreach my $c (Connection->get_all_connections()) {
        my $s = $c->get_socket();
        my ($rd_last_ts, $wr_last_ts) = $c->get_heartbeats();
        my $tmo_rd_dl = $to_read->exists($s)
                      ? $rd_last_ts + IDLE_TMO - $now : $tmo;
        my $tmo_wr_dl = $to_write->exists($s)
                      ? $wr_last_ts + WR_STALL_TMO - $now : $tmo;
        $tmo = min($tmo, max(1, $tmo_rd_dl), max(1, $tmo_wr_dl));
    }
    undef $tmo if $tmo == $inf;
    my $tmo_tx = (defined $tmo) ? "for $tmo seconds" : "indefinitely";
    debug("Shall wait for ready network socket(s) $tmo_tx");
    # the timeout is now optimal: the closest deadline, if any

    my ($rdr, $wrr) =
        grep {defined} (IO::Select->select($to_read, $to_write, undef, $tmo), ([])x2);

    my @rdr = Connection->get_connections_list_by_sockets($rdr);
    my @wrr = Connection->get_connections_list_by_sockets($wrr);
    if (first {$_ == $listening_socket} @{$rdr}) {
        accept_new($listening_socket);
    }
    return \@rdr, \@wrr, $to_read, $to_write;
}

my @uniq_refs;
sub get_uid {
    my $uniq_arrayref = [];
    push @uniq_refs, $uniq_arrayref;
    my $uid = sprintf '%016LX', refaddr $uniq_arrayref;
    1 while $uid =~ s/([0-9a-f]+)([0-9a-f]{4})/$1-$2/imsx;
    return $uid;
}

{
    # internal buffer for async commands' results; structured as
    # $UID => {ts => $startedat, PID => $PID, data => $data, completed => 0|1}
    my %async_result;

    # structured as {$PID => {uid => $UID, status => $CHILD_ERROR}}
    my %child_status;

    sub REAPER {
        while (1) {
            my $pid = waitpid(-1, WNOHANG);
            last if $pid < 0;
            my $ce = $CHILD_ERROR;
            last if ! WIFEXITED($ce);

            my $tx = "reaped $pid";
            $tx .= ($ce ? " with exit $ce" : q{});
            debug($tx);

            next if ! exists $child_status{$pid};
            $child_status{$pid}{status} = $ce;
        }
        $SIG{CHLD} = \&REAPER;  # loathe SysV
    }

sub handle_protocol {
    my $arg = shift;
    my $output = q{};

    my ($command, $client) = @{$arg}{qw( command client_connection )};

    $command =~ s/\A \s+//msx;
    $command =~ s/\s+ \z//msx;

    given ($command) {
        when ($QUIT) {
            $output = "See you later.$CRLF";
            $client->get_socket()->shutdown(0);     # close the read end
        }

        when (/\A $STATUS \s+ (\S+) \z/msx) {
            my $uid = $1;
            $output = "Unknown UID $uid.";
            my $entry = exists $async_result{$uid}
                    ? $async_result{$uid}
                    : {};
            my $data = $entry->{data};
            if ($data) {
                $output = "Status:\n$data->{exco}\n\nOutput:\n$data->{output}";

            }
            elsif ((my $pid = $entry->{PID}) and not $entry->{completed}) {
                my $kst = kill 0, $pid;
                $output = $kst
                        ? "UID $uid command is still running, try later.\n"
                        : "Waiting for final data from UID $uid command.\n";
            }
            $output = join $CRLF, split /\r?\n/msx, $output;
            $output .= $CRLF;
            $output .= $PROMPT;
        }

        when (/\A $FORGET \s+ (\S+) \z/msx) {
            my $uid = $1;
            my $entry = delete $async_result{$uid};
            my $pid = $entry && $entry->{PID};
            delete $child_status{$pid} if $pid;
            $output = "Ok.$CRLF";
            $output .= $PROMPT;
        }

        when (/\A $RESULT \s+ (\S+) \s+ (\S+) \z/msx) {
            my ($uid, $frozen) = ($1, $2);
            if ($async_result{$uid} and not $async_result{$uid}{completed}++) {
                $async_result{$uid}{data} = thaw decode_base64 $frozen;
            }
            $output = q{};
        }

        when ([$LIST_BLOCK, $LIST_NETIF, $SHOW_MEM,]) {
            my $uid = get_uid();
            # FIXME TODO for later: add throttling to prevent DoS/fork bombs
            my $new_record = schedule_async({command => $_, uid => $uid,});

            if (not $new_record) {
                $output = "Service unavailable at this time."
                        . " Try again later.$CRLF";
            } else {
                $output = $uid . $CRLF;
                $async_result{$uid} = $new_record;
            }
            $output .= $PROMPT;
        }

        default {
            my $cmdlist = join q{, } => @help;
            my $details = "$STATUS and $FORGET accept a UID parameter.";
            $output = "Valid commands are: $cmdlist.$CRLF$details$CRLF";
            $output .= $PROMPT;
        }
    }
    return $output;
}

sub schedule_async {
    my $arg = shift;
    my ($command, $uid) = @{$arg}{qw(command uid)};

    my $child_pid = fork;
    if ($child_pid < 0) {
        # service unavailable (EAGAIN) or out of memory or the like.
        # Try to preserve the whole server and other clients. Don't die.
        err("fork: $ERRNO");
    }
    elsif ($child_pid) {
        return {ts => time, PID => $child_pid, data => undef, completed => 0};
    }

    # Child process
    local $SIG{CHLD} = 'DEFAULT';
    local %ENV;
    POSIX::setsid;      # for kill in forget_stale_async

    # NB, could as well add a simple alarm() for timing out
    my ($exco, $output) = (-1, q{});
    my $handle_err =
        sub {
            my ($cmd, $out) = @_;
            $exco = $CHILD_ERROR;
            if ($exco) {
                async_result({uid => $uid,
                              data => {exco => $exco,
                                       output => "$cmd:\n$out",},
                            });
                leave();
            }
            return;
        };

    my $commify =
        sub {                   # perldoc perlfaq5
            my $copy = shift;
            1 while $copy =~ s/^([-+]?\d+)(\d{3})/$1,$2/;
            return $copy;
        };

    my $untaint =
        sub {
            my $output = shift;
            my ($result) = ($output =~ m/\A (.+) \z/msx);
            return $result;
        };

    given ($command) {
        when ($LIST_BLOCK) {
            my @result;
            my $otmpl = "%12s    %24s";

            unless ($lsblk and ($udevadm or $udevinfo) and $blockdev) {
                async_result({uid => $uid,
                              data => {exco => $exco,
                                       # FIXME TODO: improve diagnostics
                                       output => "some tools are missing",},
                            });
                leave();
            }

            $udevinfo = "$udevadm info" if $udevadm;

            my $lsblk_out = `$lsblk -abilno KNAME 2>&1`;
            $handle_err->($lsblk, $lsblk_out);
            chomp $lsblk_out;
            my @dev = split /\n/, $untaint->($lsblk_out);
            my @errors;
            foreach my $dev (sort @dev) {
                my $o = `$udevinfo --root --query=property --name=$dev 2>&1`;
                $handle_err->($udevinfo, $o);
                my ($dn) = ($o =~ m/^\s*DEVNAME\s*=\s*(\S+)/msx);
                my $size = `$blockdev --getsize64 $dn 2>&1`;
                $exco = $CHILD_ERROR;
                chomp $size;
                if ($exco) {
                    push @errors, "$blockdev (command status=$exco):\n$size";
                    next;
                }
                my $pretty_size = $commify->($size);
                push @result, sprintf $otmpl => $dev, $pretty_size;
            }
            $otmpl =~ s/([%])(\d+)(\S)/$1-$2$3/g;
            my $hl = sprintf $otmpl => "Block device", "Size (bytes)";
            unshift @errors, "\nErrors:" if @errors;
            my $result = join qq{\n} => @result, @errors;
            async_result({uid => $uid,
                          data => {exco => 0,
                                   output => "$hl\n$result",},
                        });
            leave();
        }
        
        when ($LIST_NETIF) {
            use autodie;
            my @netifs;
            eval {
                open my $fh, '<', '/proc/net/dev';
                @netifs = <$fh>;
                shift @netifs; shift @netifs;
                for (@netifs) { s/\A \s* (\S+) [:] .+ /$1/msx; }
                close $fh;
                $exco = 0;
                1;
            } or
                do {
                    async_result({uid => $uid,
                                  data => {exco => -1,
                                           output => "exception: $EVAL_ERROR",},
                                });
                    leave();
                };

                my $ls = join q{ } => sort @netifs;
                async_result({uid => $uid,
                              data => {exco => $exco,
                                       output => "Network interfaces:\n$ls",},
                            });
        }

        when ($SHOW_MEM) {
            my $o = `$free -b 2>&1`;
            $handle_err->($free, $o);
            (undef, my $total_line, my $free_line) = split /\n/ => $o;
            my $total = 0 + (split /\s+/ => $total_line)[1];
            my $free  = 0 + (split /\s+/ => $free_line)[3];
            my $used = $total - $free;      # not quite exact...
            my $output = "Total: @{[ $commify->($total) ]} bytes\n"
                       . "Used:  @{[ $commify->($used) ]} bytes\n"
                       . "Free:  @{[ $commify->($free) ]} bytes\n";

            chomp $o;
            $output .= "\nfree -b output follows verbatim:\n$o";
            async_result({uid => $uid,
                          data => {exco => $exco,
                                   output => $output,},
                        });
        }
    }
    leave();
}

sub async_result {
    my $arg = shift;
    my ($uid, $data,) = @{$arg}{qw( uid data )};

    my $client = IO::Socket::INET->new( Proto     => 'tcp',
                                        PeerHost  => 'localhost',
                                        PeerPort  => PORT_NUMBER,
                                        Blocking  => 1,
                                      );

    my $linger = pack("ii", 1, 5);      # 5s for connection to flush
    $client->sockopt(SO_LINGER, $linger) or croak "sockopt: $ERRNO"; 

    $client->shutdown(0);               # I won't read prompt etc.

    my $conn = Connection->new({socket => $client, bufsize => BUFSIZE,});

    my $frozen = freeze $data;
    my $encoded = encode_base64 $frozen, '#';
    my $tx = "$RESULT $uid $encoded$CRLF";
    my $to_write = IO::Select->new($client);
    $conn->send($tx);
    while ($conn->has_more_outgoing_data()) {
        my ($rdr, $wrr) = IO::Select->select(undef, $to_write, undef, 1);
        $conn->send(q{}) if $wrr;
    }
    $client->blocking(1);
    $client->flush();
    $client->shutdown(1);
    $client->shutdown(2);
    $client->close();
}

sub forget_stale_async {
    my $now = time;
    my $kill_started_before = $now - ASYNC_TMO;

    my @uids = keys %async_result;
    foreach my $uid (@uids) {
        my $entry = $async_result{$uid};
        next if $entry->{completed} or $entry->{ts} > $kill_started_before;
        my $pid = $entry->{PID};

        debug("killing the stale process group $pid");
        my $kst = kill -9 => $pid;
        my $missing = $!{ESRCH};
        warning("kill -9 => $pid: $ERRNO") unless $kst;

        if ($kst or $missing) {
            delete $async_result{$uid};
            delete $child_status{$pid};
        }
    }
}
}

sub ensure_singleton {
    # remember IPC::Lockfile
    open our $LOCKFILE, '<', $PROGRAM_NAME  ## no critic
      or croak "Unable to create the lockfile $PROGRAM_NAME: $ERRNO";
    flock $LOCKFILE, LOCK_EX | LOCK_NB or croak "$PROGRAM_NAME is running!";

    # reset the close-on-exec flag. This prevents recycling the server
    # until all children should go off.
    my $lffl = fcntl $LOCKFILE, F_GETFD, 0;
    fcntl $LOCKFILE, F_SETFD, $lffl & ~FD_CLOEXEC;

    END {
        our $LOCKFILE;
        if ( $LOCKFILE ) {
            close $LOCKFILE;
        }
    }
    return;
}

sub init_logger {
    my $silent = shift;
    my $ident = basename $PROGRAM_NAME;
    my $lo = Log->new({ident => $ident, facility => LOG_USER()});
    $lo->make_log_functions();
    debug("$ident has started") if not $silent;
    return;
}

sub daemonize {
    # daemonization, thanks to ISBN 5-8206-00300-4
    $SIG{TTOU} = $SIG{TTIN} = $SIG{TSTP} = $SIG{PIPE} = 'IGNORE';
    # NB, with IGNOREd SIGPIPE above, be ready to handle $!{EPIPE} from all
    # syswrite and close!

    my $child_pid = fork;
    if ( $child_pid < 0 ) {
        croak "fork: $ERRNO";
    } elsif ($child_pid) {
        leave();        # the foreground process leaves here.
    }

    my $stderr_capturer_pid = open my $new_stderr_fh, '|-';
    unless (defined $stderr_capturer_pid) {
        croak "fork: $ERRNO";
    }

    $new_stderr_fh->autoflush(1);
    POSIX::setsid;

    if ( $stderr_capturer_pid ) {
        waitpid $stderr_capturer_pid, 0;    # no zombies please
    } else {
        # fork a grandchild; let it become a son of init
        my $grandchild_pid = fork;
        if ( $grandchild_pid < 0 ) {
            croak "fork: $ERRNO";
        } elsif ($grandchild_pid) {
            leave();    # the intermediate process leaves here.
        }

        # this is STDERR capturer for our daemon.
        init_logger('silent');
        for ( 1 .. 2 ) { POSIX::close $_ }
        open STDOUT, '>', File::Spec->devnull();
        open STDERR, '>&=', 1;
        local @ARGV;
        while (<>) {
            warning($_);
        }
        Log->close_logger('silent');
        leave();
    }

    our $LOCKFILE;
    my %dont_close = map { ( fileno $_ ) => 1 } ( $LOCKFILE, $new_stderr_fh );
    foreach ( 0 .. ( POSIX::sysconf(POSIX::_SC_OPEN_MAX) || 1024 ) ) {
        POSIX::close $_ unless $dont_close{$_};
    }
    open STDIN,  '<',  File::Spec->devnull();
    open STDOUT, '>',  File::Spec->devnull();
    open STDERR, '>&=', fileno $new_stderr_fh;

    chdir File::Spec->rootdir();
    umask 0;
    Log->close_logger('silent');
    init_logger('silent');
    return;
}

# leaves (terminates the execution) with no dtors and END blocks
sub leave {
    local %ENV;
    my ( $perl ) = ($EXECUTABLE_NAME =~ m/\A (.+) \z/msx);
    my ( $pid )  = ($PID =~ m/\A (\d+) \z/msx);
    exec $perl, '-e', 'exit 0' or kill -9 => $pid;
    return;
}

{
    my ($instance, $ident);
    package Log;    # FIXME: try Log::Agent

    use autodie;
    use sigtrap;

    use Sys::Syslog qw( :DEFAULT :standard :macros );

    sub new {
        my ($invocant, $arg) = @_;
        my $self = $instance
            ||= do {
                    my $class = (ref $invocant) || $invocant;
                    $ident = $arg->{ident};
                    bless \do {my $o} => $class;
                   };

        openlog $ident, 'cons,ndelay,pid', $arg->{facility};
        return $self;
    }

    sub close_logger {
        my ($self, $silent) = @_;
        debug("$ident has completed") if not $silent;
        closelog();
        return;
    }

    sub DESTROY {
        my $self = shift;
        if ($instance) {
            $instance->close_logger();
            undef $instance;
        }
        return;
    }

    sub _get_log_args { shift; return ( (@_ > 1) ? @_ : @{[ '%s', @_ ]} ) }
    sub debug   { return syslog LOG_DEBUG(),   _get_log_args @_ }
    sub info    { return syslog LOG_INFO(),    _get_log_args @_ }
    sub warning { return syslog LOG_WARNING(), _get_log_args @_ }
    sub err     { return syslog LOG_ERR(),     _get_log_args @_ }

    sub make_log_functions {
        my @lfn = qw( debug info warning err );
        my $caller_pkg = caller 1;
        no warnings qw( redefine once );
        for my $fn (@lfn) {
            my $code = sub { return Log->$fn( @_ ); };
            no strict 'refs';   ## no critic
            *{"$caller_pkg\::$fn"} = $code;
        }
        return;
    }
}

# inside-out object, see Ch.##15-16 in Damian's PBP book.
{
    my (%socket_of, %bufsize_of, %rd_buf_of, %wr_buf_of,
        %rd_heartbeat_of, %wr_heartbeat_of, %instance_of,);

    package Connection;
    use constant MAX_BUF_SIZE => 1_048_576;     # bytes

    use Carp;
    use English qw( -no_match_vars );
    use List::Util qw(first max min);
    use Scalar::Util qw( refaddr );

    sub ident { goto \&refaddr; }

    sub new {
        my ($invocant, $arg) = @_;

        my $class = (ref $invocant) || $invocant;
        my $self = bless \do {my $o} => $class;
        my $id = ident $self;

        $socket_of{$id} = my $socket = $arg->{socket};
        $socket->autoflush(1);
        $socket->blocking(0);
        $bufsize_of{$id} = $arg->{bufsize};
        $rd_buf_of{$id} = []; $wr_buf_of{$id} = [];
        $rd_heartbeat_of{$id} = $wr_heartbeat_of{$id} = time;
        return $instance_of{$id} = $self;
    }

    sub DESTROY {
        my $self = shift;
        my $id = ident $self;

        if (my $socket = delete $socket_of{$id}) {
            $socket->flush(); $socket->close();
        }

        foreach my $datum (\%rd_buf_of, \%wr_buf_of, \%rd_heartbeat_of,
                           \%wr_heartbeat_of, \%instance_of,
                          )
        {
            delete $datum->{$id};
        }
        return;
    }

    sub close {     ## no critic
        my $self = shift;
        my $id = ident $self;
        my $socket = delete $socket_of{$id};
        $socket->flush(); $socket->close();
        delete $instance_of{$id};
        return;
    }

    sub get_all_sockets {
        return @socket_of{sort keys %socket_of};
    }
    sub get_all_connections {
        return values %instance_of;
    }

    sub find {
        my ($class, $socket) = @_;
        my $match = first { $socket_of{$_} == $socket } keys %socket_of;
        return $instance_of{$match};
    }

    sub get_connections_list_by_sockets {
        my ($self, $arrayref_sockets) = @_;
        my %socket_to_id = reverse %socket_of;      # they're unique
        my @ids = grep {defined} @socket_to_id{@{$arrayref_sockets}};
        return @instance_of{@ids};
    }

    sub get_id     { return ident $_[0] }
    sub get_socket { return $socket_of{ident $_[0]} }

    sub get_heartbeats {
        my $self = shift;
        my $id = ident $self;
        return ($rd_heartbeat_of{$id}, $wr_heartbeat_of{$id},);
    }

    sub has_more_outgoing_data {
        my $self = shift;
        my $wb = $wr_buf_of{ident $self};
        return ($wb and first {length} @{$wb});
    }
    sub discard_outgoing_data {
        my $id = ident shift;
        Log->warning("Discarded any data outgoing to ID=$id");
        delete $wr_buf_of{$id};
        return;
    }

    # postcondition: heartbeat updated on success. Success is deemed when
    # a progress is made (i.e. a chunk is written).
    sub send {      ## no critic
        my ($self, $buf) = @_;
        my $id = ident $self;
        my $socket = $socket_of{$id};
        my $whole_buf = $wr_buf_of{$id};
        return if not $whole_buf
                or not ($socket->opened() and $socket->connected());

        use bytes;
        my $size = $bufsize_of{$id};

        push @{$whole_buf}, substr $buf, 0, $size, q{} while length $buf;

        my ($short_of, $written) = (0, 0);
        while (defined(my $chunk = shift @{$whole_buf})) {
            my $len = length $chunk;
            next unless $len;

            my $rv = $socket->syswrite($chunk);
            if (!defined($rv) && ($!{EAGAIN} || $!{EWOULDBLOCK})) {
                # would block
                $short_of += $len;
            } elsif (!defined($rv)) {
                my $fdnum = $socket->fileno();
                Log->err("Got errno='$ERRNO', extended OS error details="
                       . "'$EXTENDED_OS_ERROR' during a write attempt of"
                       . " $len octets into FD=$fdnum."
                       );
            } elsif ($rv != $len) {
                # incomplete write
                $written += $rv;
                substr $chunk, 0, $rv, q{};
                $short_of += $len - $rv;
            } else {
                # successfully wrote
                $written += $len;
                next;
            }

            unshift @{$whole_buf}, $chunk;
            last;
        }

        if (not $short_of) { $wr_heartbeat_of{$id} = time }
        return $written;
    }

    sub is_eof  { return not $rd_buf_of{ident $_[0]} }
    sub set_eof { delete $rd_buf_of{ident $_[0]}; return; }

    # postcondition: heartbeat updated on success. Success is deemed when
    # a progress is made (i.e. a newline is discovered in the input stream).
    # Return value: a list of lines, each one ending with a line terminator \n
    # An empty value if no \n has been seen in the stream.
    sub recv {      ## no critic
        my ($self) = @_;
        my $id = ident $self;
        my $socket = $socket_of{$id};
        my $whole_buf = $rd_buf_of{$id};

        if ($self->is_eof()
            or not ($socket->opened() and $socket->connected())
           )
        {
            $self->set_eof();
        }

        use bytes;
        my @result;
        my $size = $bufsize_of{$id};

        my $read = 0;
        while (1) {
            my $rv = $socket->sysread(my $chunk, $size);
            if (!defined($rv) && ($!{EAGAIN} || $!{EWOULDBLOCK})) {
                # would block
                last;
            } elsif (!defined $rv) {
                my $fdnum = $socket->fileno();
                Log->err("Got errno='$ERRNO', extended OS error details="
                       . "'$EXTENDED_OS_ERROR' during a read attempt of"
                       . " up to $size octets from FD=$fdnum."
                       );
            } elsif ($rv == 0) {
                # EOF, hence no more data shall be; current data are returned
                $self->set_eof();
                last;
            } else {
                # successfully read
                push @{$whole_buf}, $chunk;
                $read += length $chunk;
            }
        }

        my $prev_buf = q{};
        while (defined(my $chunk = shift @{$whole_buf})) {
            my $combined = join(q{} => grep { defined } ($prev_buf, $chunk));
            my @interim = split /(?<=\n)/msx, $combined, -1;
            $prev_buf = pop @interim;   # it has no \n hence gets requeued
            push @result, @interim;
        }

        if (MAX_BUF_SIZE < length $prev_buf) {
            # forbid too lengthy fruitless buffer overruns
            $self->set_eof();
            return;
        }

        @{$whole_buf} = ($prev_buf,);
        if (@result) { $rd_heartbeat_of{$id} = time }
        $self->set_eof() if not $read;
        return @result;
    }
}

# vim: set et ts=4:
