#!/usr/bin/env perl
#
# fetch.pl (asynchronous version)
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

use v5.38;

use strict;
use warnings;
use diagnostics;

use autodie;
use sigtrap;

use constant BUFSIZE     =>    512;     # bytes
use constant CONN_TMO    =>     30;     # seconds for connection initiation
use constant READ_TMO    =>      5;     # seconds for inbound chunk of data
use constant WR_STALL_TMO=>      5;     # seconds for response progress

use Carp qw( :DEFAULT cluck );
use Errno;
use English qw( -no_match_vars );
use File::Basename qw( basename );

use Getopt::Std;

use IO::Poll qw(POLLIN POLLOUT POLLERR POLLHUP);
use IO::Socket;
use List::Util qw(first max min);
use Scalar::Util qw( refaddr );
use Socket qw( :DEFAULT :crlf );
use Sys::Syslog qw( :DEFAULT :standard :macros );

our ($opt_h, $opt_u);
_run() unless caller;

#########

sub do_fetch {
    my ($method, $host, $port, $path) = @_;
    my $maybe_ua = q{};
    for ($opt_u || q{}) {
        m/^\s*([^\n]+)/ && do { $maybe_ua = "\nUser-Agent: $1"; };
    }

    my $http_request_message = <<EOM;
$method $path HTTP/1.1
Host: $host$maybe_ua
Accept: text/html;charset=utf-8, text/plain;charset=utf-8, application/xhtml+xml, application/xml;q=0.9, application/json;q=0.8, */*;q=0.1
Accept-Charset: utf-8
Accept-Encoding: identity
Connection: close
Content-Length: 0

EOM

    my $conn = initiate_connection($host, $port);

    $conn->wait_connection_established()
        and Log->info("Connection established to $host:$port");

    # it is line-oriented, hence the split
    my $req_lines = [map { "$_\r\n" } split qq{\n}, $http_request_message, -1];
    my %requests = ($conn->get_id() => $req_lines);

    my $http_parser = HTTP::Parser->new();
    my %http_parsers = ($conn->get_id() => $http_parser );

=for plural %requests:

        map {
            $_->get_id() => [map { "$_\r\n" } split qq{\n}, $http_request_message, -1]
        } @{[ $conn ]};

=cut

    event_loop([$conn], \%requests, \%http_parsers);
    my $code = $http_parser->get_http_status_code();
    my $status_text = $http_parser->get_http_status_text();
    my @raw_headers = $http_parser->get_raw_headers();
    my @normalized_headers = $http_parser->get_normalized_headers();
    my @body = $http_parser->get_body();
    if ($http_parser->is_chunked()) {
        use Data::Dumper;
        my @chunks = $http_parser->get_chunks();
        pop @chunks;    # remove the final (zero/empty) chunk
        @body = ('chunked-body', 'dump follows', Dumper(\@chunks));
    }
    return ($code, $status_text, \@raw_headers, \@normalized_headers, \@body);
}


sub parse_url {
    my $url = shift;
    for ($url) {
        s/^\s+//;
        s/\s+$//;
    }
    die 'empty URL' unless length $url;
    die 'HTTPS is not supported at the moment' if $url =~ m{^https://}i;

    # appendix B. of RFC2396:
    my $uri_re = qr{^(([^:/?#]+):)?(//([^/?#]*))?([^?#]*)(\?([^#]*))?([#](.*))?};
    my  ( undef
        , $scheme
        , undef
        , $authority
        , $path
        , undef
        , $query
        , undef
        , $fragment
        ) = $url =~ m/$uri_re/;

    $scheme ||= 'http';
    die 'It is only HTTP scheme that is supported at the moment' if 'http' ne lc $scheme;

    die 'Query and Fragment URI parameters are ignored for now' if $query || $fragment;
    my ($host, $port) = $authority =~ m/^([^:]+)([:](\d+))?$/;

    my $default_port;
    for ($scheme) {
        /^http$/i && do {
            $default_port = 80;
            last;
        };

        /^https$/i && do {
            $default_port = 443;
            last;
        };

        die "Unknown URI scheme [$scheme]";
    }
    $port ||= $default_port;

    say "Shall fetch path=$path from $host:$port with \L$scheme\E protocol";
    return ($scheme, $host, $port, $path)
}

BEGIN {
    my $tm  = ${^TAINT};
    my $lbn = $ENV{LD_BIND_NOW};
    my $dlnl= $ENV{PERL_DL_NONLAZY};
    # For debugging
    carp "Taint mode is @{[ $tm ? 'on' : 'off' ]}";
    carp "LD_BIND_NOW is @{[ $lbn ? q{} : 'not ' ]}set";
    carp "PERL_DL_NONLAZY is @{[ $dlnl ? q{} : 'not ' ]}set";

    if ( not $tm or not $lbn or not $dlnl ) {
        # helps in reducing jitters in runtime
        $ENV{LD_BIND_NOW} = 1;
        $ENV{PERL_DL_NONLAZY} = 1;
        exec $EXECUTABLE_NAME, '-T', $PROGRAM_NAME, @ARGV or kill -9 => $PID;
    }

    # sane PATH for taint mode.
    $ENV{PATH} = '/usr/sbin:/usr/bin:/sbin:/bin:/opt/bin';
}

sub init_logger {
    my $silent = shift;
    my $ident = basename $PROGRAM_NAME;
    my $lo = Log->new({ident => $ident, facility => LOG_USER()});
    $lo->make_log_functions();
    debug("$ident has started") if not $silent;
    return;
}

# identity function
sub handle_line { return $_[0]; }

## main
{
    package main;

    sub HELP_MESSAGE() {
        STDOUT->autoflush(1);

        say <<USAGE;
Usage: $PROGRAM_NAME [-h] [-u <user-agent>] <url>
    -h forces HEAD request.
    -u allows to specify User-Agent header.
USAGE

        leave();
    }

    # leaves (terminates the execution) with no dtors and END blocks
    sub leave {
        local %ENV;
        my ( $perl ) = ($EXECUTABLE_NAME =~ m/\A (.+) \z/msx);
        my ( $pid )  = ($PID =~ m/\A (\d+) \z/msx);
        exec $perl, '-e', 'exit 0' or kill -9 => $pid;
        return;
    }
}

## Log
{
    my ($instance, $ident);
    package Log;

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

## Connection
# inside-out object, see Ch.##15-16 in Damian's PBP book.
{
    my (%socket_of, %bufsize_of, %rd_buf_of, %wr_buf_of,
        %rd_heartbeat_of, %wr_heartbeat_of, %instance_of,
        %concluded,);

    package Connection;
    use constant MAX_BUF_SIZE => 1_048_576;     # bytes

    use Carp;
    use English qw( -no_match_vars );
    use IO::Poll qw(POLLIN POLLOUT POLLERR POLLHUP);
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
        $concluded{$id} = 0;
        return $instance_of{$id} = $self;
    }

    sub DESTROY {
        my $self = shift;
        my $id = ident $self;

        if (my $socket = delete $socket_of{$id}) {
            $socket->flush(); $socket->close();
        }

        foreach my $datum (\%rd_buf_of, \%wr_buf_of, \%rd_heartbeat_of,
                           \%wr_heartbeat_of, \%instance_of, \%bufsize_of,
                           \%concluded,
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

    sub get_id     { return ident $_[0] }
    sub get_socket { return $socket_of{ident $_[0]} }

    sub get_heartbeats {
        my $self = shift;
        my $id = ident $self;
        return ($rd_heartbeat_of{$id}, $wr_heartbeat_of{$id},);
    }

    sub is_viable {
        my $self = shift;
        my $socket = $self->get_socket();
        return ((defined $socket) && $socket->opened() && $socket->connected());
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
        return if not $whole_buf or not $self->is_viable();

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

    sub is_eof  { return $concluded{ident $_[0]} }
    sub set_eof { ++$concluded{ident $_[0]}; return; }

    sub has_more_data {
        my ($self) = @_;
        my $id = ident $self;
        my $socket = $socket_of{$id};
        my $whole_buf = $rd_buf_of{$id};
        return (defined $whole_buf) && @{ $whole_buf };
    }

    sub get_final_chunk {
        my ($self) = @_;
        return unless $self->has_more_data();
        return @{ $rd_buf_of{ident $self} };
    }

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
            $prev_buf ||= q{};
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

    sub wait_connection_established {
        my $self = shift;
        my $id = ident $self;
        my $socket = $socket_of{$id};

        unless ($socket->opened() and $socket->connected()) {
            my $poll = IO::Poll->new()
                or croak "Unable to set up IO::Poll: errno=$!, os_error=$^E";
            $poll->mask($socket => POLLOUT);
            $poll->poll(main::CONN_TMO)
                or croak "Connection timeout: errno=$!, os_error=$^E";
        }
    }
}

## HTTP parser
# Shortcomings (easy to overcome):
#  1. headers normalization is crippled (i.e. nor escaping nor quoting
#      are supported). Header values are barely handled.
#  2. UTF-8 parsing attempts aren't there at all (think "use bytes"). Cyrillic
#      letters may fail to work for now.
{
    package HTTP::Parser;

    my (%headers_of, %body_of, %http_status_code_of, %is_chunked, %seen_octets,
        %content_length, %http_status_text_of, %seen_blank_line_of,
        %accumulator_of, %chunks_of, %chunk_idx_of, %expected_octets_cnt,
        %chunks_concluded_for,
       );

    use Scalar::Util qw( refaddr );

    sub ident { goto \&refaddr; }

    sub new {
        my ($invocant, $arg) = @_;

        my $class = (ref $invocant) || $invocant;
        my $self = bless \do {my $o} => $class;
        my $id = ident $self;

        $headers_of{$id} = [];
        $body_of{$id} = [];
        $http_status_code_of{$id} = 599;
        $http_status_text_of{$id} = q{Not evaluated};

        $seen_blank_line_of{$id} = \do {my $o};
        $accumulator_of{$id} = $headers_of{$id};
        $is_chunked{$id} = 0;
        $content_length{$id} = undef;
        $seen_octets{$id} = do {
            use bigint;
            0;
        };
        $chunks_concluded_for{$id} = undef;
        $chunks_of{$id} = [ [] ];
        $chunk_idx_of{$id} = 0;
        $expected_octets_cnt{$id} = undef;
        return $self;
    }

    sub DESTROY {
        my $self = shift;
        my $id = ident $self;

        $seen_blank_line_of{$id} ||= \do {my $o};
        delete $seen_blank_line_of{$id};

        foreach my $datum (\%headers_of, \%body_of, \%http_status_code_of,
                            \%chunks_of, \%chunk_idx_of, \%http_status_text_of,
                            \%seen_blank_line_of, \%seen_octets,
                            \%expected_octets_cnt, \%accumulator_of,
                            \%is_chunked, \%content_length,
                            \%chunks_concluded_for) {
            delete $datum->{$id};
        }
        return;
    }

    sub get_raw_headers {
        my $self = shift;
        return @{ $headers_of{ident $self} };
    }

    sub get_normalized_headers {
        my $self = shift;
        my @result;
        my %interim;
        my @headers_order;
        my $last_seen_header;
        my @raw_headers = @{ $headers_of{ident $self} };
        shift @raw_headers;     # remove status line as it is not a header.
        for my $header_line (@raw_headers) {
            if ($last_seen_header && (my ($continuation) = ($header_line =~ m/\A \s+ (.*)/msx))) {
                $interim{$last_seen_header} ||= [ q{} ];
                $interim{$last_seen_header}[-1] .= $continuation;
                next;
            }

            my ($header_name, $header_value) = ($header_line =~ m/\A \s* ([^:]+?) \s* [:] \s* (.*?) \s* \z/msx);
            next unless defined $header_name;

            my $normalized_header_name = lc $header_name;
            $last_seen_header = $normalized_header_name;
            $interim{$last_seen_header} ||= [ ];
            push @{ $interim{$last_seen_header} }, $header_value;
            push @headers_order, $last_seen_header;
        }

        for my $header_name ( @headers_order ) {
            my $values_ref = delete $interim{ $header_name } || next;
            my @all_values = @{ $values_ref };
            push @result, map { "$header_name: $_" } @all_values;
        }
        return @result;
    }

    sub get_body {
        my $self = shift;
        return @{ $body_of{ident $self} };
    }

    sub get_http_status_code {
        my $self = shift;
        return $http_status_code_of{ident $self};
    }

    sub get_http_status_text {
        my $self = shift;
        return $http_status_text_of{ident $self};
    }

    sub is_chunked {
        my $self = shift;
        return $is_chunked{ident $self};
    }

    sub get_chunks {
        my $self = shift;
        my $id = ident $self;
        die unless $is_chunked{$id};
        return @{ $chunks_of{$id} };
    }

    sub parse_lines {
        my ($self, $lines_ref) = @_;
        my $id = ident $self;

        goto &FSM_parse_lines_chunked if $is_chunked{$id};

        my $accumulator = $accumulator_of{$id};
        my $seen_blank_line_ref = $seen_blank_line_of{$id};
        my $is_header = 1;
        while (@{ $lines_ref }) {
            my $line = shift @{ $lines_ref };
            unless ($is_header) {
                use bytes;
                $seen_octets{$id} += length $line;  # raw line length
            }

            $line =~ s/\r\n \z//msx;
            unless (length $line) {
                ${ $seen_blank_line_ref } ||= 1;
                $accumulator = [];  # don't store the blank line for headers.
            }

            # range operator FTW in scalar context to distinguish headers & body
            $is_header = (!${ $seen_blank_line_ref })..${ $seen_blank_line_ref };

            if ($is_header && ($line =~ m/\A transfer-encoding \s* [:] \s* chunked \s* \z/imsx)) {
                die 'That cannot be! (both content-length and chunked enconding encountered)'
                    if $content_length{$id};
                push @{ $headers_of{$id} }, $line;
                $is_chunked{$id} = 1;
                goto &FSM_parse_lines_chunked;
            } elsif ($is_header && (my ($cl) = ($line =~ m/\A content-length \s* [:] \s* (\d+) \s* \z/ims))) {
                $content_length{$id} = $cl;
            }

            $accumulator = $body_of{$id} unless $is_header;

            push @{ $accumulator }, $line;
            last if ($content_length{$id} and ($seen_octets{$id} >= $content_length{$id}));
        }

        my $status_line = $headers_of{$id}[0] || q{};
        my ($code, $status_text,) = $status_line =~ m{\A \s* HTTP/[.\d]+ \s+ (\d+) \s+ (.+) \z}msx;

        $http_status_code_of{$id} = $code;
        $http_status_text_of{$id} = $status_text;
        return $self;
    }

    sub FSM_parse_lines_chunked {
        my ($self, $lines_ref) = @_;
        my $id = ident $self;
        $self->FSM_headers_readup($lines_ref);
        return $self;
    }

    sub FSM_headers_readup {
        my ($self, $lines_ref) = @_;
        my $id = ident $self;

        my $seen_blank_line_ref = $seen_blank_line_of{$id};
        goto \&FSM_read_chunk if @{ $lines_ref } && ${ $seen_blank_line_ref };

        ${ $seen_blank_line_ref } = 0;
        unless (${ $seen_blank_line_ref }) {
            while (@{ $lines_ref }) {
                my $line = shift @{ $lines_ref };
                $line =~ s/\r\n \z//msx;
                unless (length $line)   {
                    # this concludes the header
                    ${ $seen_blank_line_ref } = 1;
                    last;
                }

                if (my ($cl) = ($line =~ m/\A content-length \s* [:] \s* (\d+) \s* \z/ims)) {
                    die 'That cannot be! Content-Length encountered during chunked encoding parsing!'
                }

                push @{ $headers_of{$id} }, $line;
            }

            if ($chunks_concluded_for{$id}) {
                my $status_line = $headers_of{$id}[0] || q{};
                my ($code, $status_text,) = $status_line =~ m{\A \s* HTTP/[.\d]+ \s+ (\d+) \s+ (.+) \z}msx;

                $http_status_code_of{$id} = $code;
                $http_status_text_of{$id} = $status_text;
                return;
            }

            goto \&FSM_read_chunk if @{ $lines_ref };
        }
    }

    sub FSM_read_chunk {
        my ($self, $lines_ref) = @_;
        my $id = ident $self;

        my $seen_blank_line_ref = $seen_blank_line_of{$id};
        last unless ${ $seen_blank_line_ref };

        my $accumulator = $chunks_of{$id}->[ $chunk_idx_of{$id} ];
        my $chunk_len = $expected_octets_cnt{$id};
        while (@{ $lines_ref }) {
            my $line = shift @{ $lines_ref };

            unless (defined $chunk_len) {
                ( $chunk_len ) = ( $line =~ m/\A ([0-9a-fA-F]+) /msx );
                $expected_octets_cnt{$id} = do {
                    use bigint;
                    hex($chunk_len);
                };

                ++$chunks_concluded_for{$id} unless $chunk_len;
                next;
            }

            {
                use bytes;
                $seen_octets{$id} += length $line;  # raw line length
            }

            $line =~ s/\r?\n \z//msx;
            push @{ $accumulator }, $line;

            if ($chunk_len and ($seen_octets{$id} >= $chunk_len)) {
                $seen_octets{$id} = 0;
                ${ $seen_blank_line_ref } = 0;  # now expect a header once again
                push @{ $chunks_of{$id} }, [];
                ++$chunk_idx_of{$id};
                last;
            }

        }

        goto \&FSM_headers_readup if @{ $lines_ref };
    }
}

sub initiate_connection {
    my ($host, $port) = @_;
    my $client = IO::Socket::INET->new( Proto     => "tcp",
                                        PeerPort  => $port,
                                        PeerHost  => $host,
                                        Blocking  => 0,
                                      );

    croak "can't setup client" unless $client;

    my $linger = pack("ii", 1, 5);      # 5s for connection to flush
    $client->sockopt(SO_LINGER, $linger) or croak "sockopt: $ERRNO"; 
    my $conn = Connection->new({socket => $client, bufsize => BUFSIZE,});
    return $conn;
}

sub event_loop {
    my ($connections, $requests, $parsers) = @_;

    # Based on Lincoln D. Stein book on Network programming
    #  (part 3 with IO::Poll).
    my $poll = IO::Poll->new()
        or croak "Unable to set up IO::Poll: errno=$!, os_error=$^E";

    $poll->mask($_ => POLLOUT | POLLERR)
        foreach map { $_->get_socket() } @{ $connections };

    while ($poll->handles()) {
        my ($rdr, $wrr, $to_read, $to_write) =
            wait_for_ready_connections({connections => $connections,
                                        requests => $requests,
                                      });
        my %newmask;
        foreach my $conn (@{$wrr}) {
            my $id = $conn->get_id();
            my $req = delete $requests->{$id} || croak "Bad request for $id";
            my $written = 0;
            foreach my $line (@{$req}) {
                $written += $conn->send($line);
            }
            if (not $written) {
                # the socket was claimed as "ready for writing" but
                # did not progress at all. This means the remote shutdown.
                # NB: SSL-aware implementation should be more permissive...
                $conn->discard_outgoing_data();
            } elsif ($conn->has_more_outgoing_data()) {
                $newmask{$conn->get_id()} = POLLOUT | POLLERR;
            } else {
                $newmask{$conn->get_id()} |= POLLIN | POLLHUP | POLLERR;
            }
        }
        foreach my $conn (@{$rdr}) {
            my $id = $conn->get_id();
            my $parser = $parsers->{$id};
            my @lines = $conn->recv();
            foreach my $line (@lines) {
                my (@thunk) = handle_line($line);
                $parser->parse_lines(\@thunk);
            }
            if ($conn->is_eof()) {
                if ($conn->has_more_data()) {
                    @lines = $conn->get_final_chunk();
                    foreach my $line (@lines) {
                        my (@thunk) = handle_line($line);
                        $parser->parse_lines(\@thunk);
                    }
                }

                unless ($conn->has_more_outgoing_data()) {
                    $poll->remove($conn->get_socket());
                    $conn->close();
                }
            } else {
                $newmask{$conn->get_id()} |= POLLIN | POLLHUP | POLLERR;
            }
        }

        # handle connections to be terminated.
        my %wait_read  = map { $_->get_id() => 1 } @{ $to_read };
        my %wait_write = map { $_->get_id() => 1 } @{ $to_write };

        my $now = time;
        foreach my $conn (Connection->get_all_connections()) {
            my $s = $conn->get_socket();

            my ($rd_last_ts, $wr_last_ts) = $conn->get_heartbeats();
            my $reason = (exists $wait_read{ $conn } and $rd_last_ts <= $now - READ_TMO)
                       ? "Idle too long"
                       : (exists $wait_write{ $conn } and $wr_last_ts <= $now - WR_STALL_TMO)
                       ? "Write stalled"
                       : q{};
            if ($reason) {
                my $id = $conn->get_id();
                Log->info("Closing connection $id due to $reason");
                $conn->close();

                # it means it shall be removed from poll
                $newmask{$id} = 0;
            }

            $poll->mask($s => $newmask{$conn->get_id()});
        }
    }
}

sub wait_for_ready_connections {
    my $arg = shift;
    my ($connections, $requests,) = @{$arg}{qw(connections requests)};

    my $to_write = [];
    my $to_read  = [];
    foreach my $c (Connection->get_all_connections()) {
        my $id = $c->get_id();
        my $s = $c->get_socket();

        my $i_have_data = (exists $requests->{$id} and @{$requests->{$id}});
           $i_have_data ||= $c->has_more_outgoing_data();
        push @{$to_write}, $c if $i_have_data;

        push @{$to_read}, $c;
    }

    my %wait_read  = map { $_->get_id() => 1 } grep { $_->is_viable() } @{ $to_read };
    my %wait_write = map { $_->get_id() => 1 } grep { $_->is_viable() } @{ $to_write };

    my $tmo = my $inf = 9**9**9;
    my $now = time;
    foreach my $c (Connection->get_all_connections()) {
        my $s = $c->get_socket();

        my ($rd_last_ts, $wr_last_ts) = $c->get_heartbeats();
        my $tmo_rd_dl = exists $wait_read{ $c->get_id() } 
                      ? $rd_last_ts + READ_TMO - $now : $tmo;
        my $tmo_wr_dl = exists $wait_write{ $c->get_id() }
                      ? $wr_last_ts + WR_STALL_TMO - $now : $tmo;
        $tmo = min($tmo, max(1, $tmo_rd_dl), max(1, $tmo_wr_dl));
    }

    my @viable_rd = grep { $wait_read{ $_->get_id() } } @{ $to_read };
    my @viable_wr = grep { $wait_write{ $_->get_id() } } @{ $to_write };
    unless (@viable_rd || @viable_wr) {
        # corner case - nothing to poll from now on.
        return [], [], $to_read, $to_write;
    }

    undef $tmo if $tmo == $inf;
    my $tmo_tx = (defined $tmo) ? "for $tmo seconds" : "indefinitely";
    info("Shall wait for ready network socket(s) $tmo_tx");
    # the timeout is now optimal: the closest deadline, if any

    my $poll = IO::Poll->new()
        or croak "Unable to set up IO::Poll: errno=$!, os_error=$^E";

    $poll->mask($_->get_socket() => POLLIN | POLLHUP | POLLERR) for @viable_rd;
    $poll->mask($_->get_socket() => POLLOUT | POLLERR) for @viable_wr;

    unless ($poll->poll($tmo)) {
        # corner case: a timeout!
        return [], [], $to_read, $to_write;
    }

    my $rdr = $poll->handles( POLLIN | POLLHUP | POLLERR );
    my $wrr = $poll->handles( POLLOUT | POLLERR );

    my (@rdr, @wrr);
    foreach my $c (Connection->get_all_connections()) {
        my $s = $c->get_socket();
        push @rdr, $c if ($poll->events( $s ) & (POLLIN | POLLHUP | POLLERR));
        push @wrr, $c if ($poll->events( $s ) & (POLLOUT | POLLERR));
    }
    return \@rdr, \@wrr, $to_read, $to_write;
}

sub _run {
    main::HELP_MESSAGE() unless getopts('hu:');
    init_logger();

    my $url = shift @ARGV or do {
        Log->err("Missing URL");
        carp 'URL must be given';
        main::HELP_MESSAGE();
    };
    my (undef, $host, $port, $path) = parse_url($url);

    my $method = $opt_h ? 'HEAD' : 'GET';
    my ($response_code, $status_text, $raw_response_headers,
        $normalized_response_headers, $response_body) = do_fetch($method, $host, $port, $path);

    say "\n\t\tHTTP Response code is $response_code";
    say "\t\tHTTP Response status text is $status_text";
    say "\t\tRaw response headers follow:";
    say $_ for @{ $raw_response_headers || [] };

    say "\n\t\tNormalized response headers follow:";
    say $_ for @{ $normalized_response_headers || [] };

    unless ($opt_h) {
        say "\n\t\tResponse content follows:";
        say $_ for @{ $response_body || [] };
    } else {
        say "\n\t\tHEAD request (no response content)";
    }
}

1;

__END__

Viable http-only sites for testing (chunked-encoding streaming included):
http://badssl.com/
http://captive.apple.com/
http://detectportal.firefox.com/success.txt
http://example.com/
http://httpforever.com/
http://info.cern.ch/
http://ip.jsontest.com/
http://neverssl.com/
http://www.httpvshttps.com/
http://www.thelegacy.de/
http://ya.ru/

# set ts=4 sw=4 et
