#!/usr/bin/env perl

# fetch.pl (synchronous version)
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

use constant CONN_TMO    =>     30;     # seconds for connection initiation
use constant READ_TMO    =>      5;     # seconds for inbound chunk of data
use constant WR_STALL_TMO=>      5;     # seconds for response progress

use Carp qw( :DEFAULT cluck );
use Errno;
use English qw( -no_match_vars );

use Getopt::Std;

use IO::Poll qw(POLLIN POLLOUT POLLERR POLLHUP);
use IO::Socket;
use Scalar::Util qw( refaddr );
use Socket qw( :DEFAULT :crlf );

our ($opt_h, $opt_u);
_run() unless caller;

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
    wait_connection_established($conn) and say "Connection established to $host:$port";

    my $req_lines = [map { "$_\r\n" } split qq{\n}, $http_request_message, -1];
    my $http_parser = HTTP::Parser->new();

    $SIG{ALRM} = sub { die 'Timeout'; };
    alarm WR_STALL_TMO;
    print { $conn } $_ for @{ $req_lines };
    alarm 0;

    alarm READ_TMO;
    {
        $conn->blocking(1);
        local $/ = undef;
        my $input = <$conn>;
        $http_parser->parse_lines([$_]) for map { "$_\n" } split /\n/, $input, -1;
    }
    alarm 0;

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
    }
}

sub wait_connection_established {
    my $socket = shift || die;
    unless ($socket->opened() and $socket->connected()) {
        my $poll = IO::Poll->new()
            or croak "Unable to set up IO::Poll: errno=$!, os_error=$^E";
        $poll->mask($socket => POLLOUT);
        $poll->poll(main::CONN_TMO)
            or croak "Connection timeout: errno=$!, os_error=$^E";
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
    return $client;
}

sub _run {
    main::HELP_MESSAGE() unless getopts('hu:');
    my $url = shift @ARGV or do {
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
