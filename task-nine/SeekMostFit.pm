# SeekMostFit.pm
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

package SeekMostFit;

use v5.38;
use strict;
use warnings;

use base qw( Exporter );

our $VERSION = 1.0;
our @EXPORT_OK = 'seek_most_matching_number_in_sorted_list';

# API

# usage: ...(LIST-where, SCALAR-what)
sub seek_most_matching_number_in_sorted_list : prototype(+$);

# Impl

use constant INF => 9 ** 9 ** 9;

sub seek_most_matching_number_in_sorted_list : prototype(+$) {
    my ($where, $what) = @_;
    die 'ARRAY reference expected' unless 'ARRAY' eq ref $where;
    die "Numeric value expected; got $what" unless _looks_like_number($what);
    die 'Exactly 2 arguments are expected!' if @_ != 2;

    return unless @{ $where };

    return 0 if ($what <= $where->[0]);
    my $right = my $rightmost = $where->$#*;
    return $right if ($what >= $where->[-1]);

    # bounds are inclusive; both corner cases checked above, so narrow by 1.
    my $left = 1;
    $right--;

    my $mid;
    my $adjacent_check;
    my $check_left = \&_check_left;
    my $check_right = \&_check_right;
    while ($right > $left) {
        $mid = $left + (($right - $left) >> 1);
        my $partition = $where->[$mid];

        # it is right-biased, i.e. provided the matching value appear multiple
        #  times in the source list, it shall approach the rightmost-one.
        # And the split be: [left, mid+1) and [mid+1, right).
        if ($what < $partition) {
            $right = $mid;
            $adjacent_check = $check_left;
        } elsif ($what > $partition) {
            $left = $mid + 1;
            $adjacent_check = $check_right;
        } else {
            return $mid;
        }
    }

    # the exact value not found; rather, what's found is the Insertion
    #  point. Here we have to recheck the adjacent positions.
    # NB: As the while loop above is constructed, it is enough to check
    #  only ONE of adjacent values (as the alternative branch gets cut
    #  off in the loop, and there is no suitable candidate there).
    push @_, $mid, abs($what - $where->[$mid]);
    goto &$adjacent_check;
}

sub _check_left {
    my ($where, $what, $best, $smallest) = @_;
    my $offset = $best - 1;
    if ($offset >= 0 and abs($where->[$offset] - $what) < $smallest) {
        return $offset;
    }
    return $best;
}

sub _check_right {
    my ($where, $what, $best, $smallest) = @_;
    my $offset = $best + 1;
    if ($offset <= $where->$#* and abs($where->[$offset] - $what) < $smallest) {
        return $offset;
    }
    return $best;
}

# perldoc perlfaq4 recipe
sub _looks_like_number {
    my $input = shift;
    for ($input) {
        if ( /^\d+\z/ ) {
            return 1;
        }

        if ( /^-?\d+\z/ ) {
            return 1;
        }

        if ( /^[+-]?\d+\z/ ) {
            return 1;
        }

        if ( /^-?(?:\d+\.?|\.\d)\d*\z/ ) {
            return 1;
        }

        if ( /^[+-]?(?=\.?\d)\d*\.?\d*(?:e[+-]?\d+)?\z/i ) {
            return 1;
        }
    }

    return;
}

package SeekMostFit::Tests;

use Benchmark qw( :hireswallclock cmpthese );

use constant SECONDS_BENCHMARKING => 30;

sub _generate {
    my $line = shift;
    my %parameters = $line =~ m/\G (\w+) = (\S+) \s* /gx;

    my $expected = $parameters{expected}
        || die 'expected not given (line=$line)';

    my $count = $parameters{count} || SeekMostFit::INF;
    my $limit = $parameters{limit} || SeekMostFit::INF;
    my $mode = $parameters{mode} || 'normal';

    our $cur = my $initial = $parameters{initial} || 0;

    my $f = $parameters{f} || die "f must be given (line=$line)";
    if ($mode eq 'bigfloat') {
        no warnings 'redefine';
        eval "
            package SeekMostFit::Tests;
            {
                use bigfloat;
                our \$cur;
                *_calc_item = sub {
                    $f;
                };
            }
        ";
    } elsif ($mode eq 'bigint') {
        no warnings 'redefine';
        eval "
            package SeekMostFit::Tests;
            {
                use bigint;
                our \$cur;
                *_calc_item = sub {
                    $f;
                };
            }
        ";
    } elsif ($mode eq 'integer') {
        no warnings 'redefine';
        eval "
            package SeekMostFit::Tests;
            {
                use integer;
                our \$cur;
                *_calc_item = sub {
                    $f;
                };
            }
        ";
    } else {
        no warnings 'redefine';
        eval "
            package SeekMostFit::Tests;
            {
                our \$cur;
                *_calc_item = sub {
                    $f;
                };
            }
        ";
    }
    my $sought = $parameters{sought}
        || die "sought must be given (line=$line)";

    my @result;
    $#result = ($count - 1) if $count < SeekMostFit::INF;
    local $_ = 0;
    my $prev = $cur;
    while (1) {
        last if $cur >= $limit || $_ >= $count;
        last if $prev > $cur || $cur < $initial;

        $prev = $cur;
        $cur = &SeekMostFit::Tests::_calc_item;
    } continue {
        $result[$_] = $cur if $cur < $limit;
        ++$_;
    }

    # overflow can happen sometimes; amend it as it violates sort order.
    for (my $idx = $#result; $idx > 0; $idx--) {
        if ($result[$idx] < $result[$idx - 1]) {
            $result[$idx] = $result[$idx - 1];
        }
    }

    return ($sought, $expected, \@result);
}

sub _main() {
    for my $line (<DATA>) {
        next if $line =~ /^\s*$/;
        next if $line =~ /^\s*#/;
        chomp $line;

        my ($sought, $expected, $list) = _generate($line);
        my $response = SeekMostFit::seek_most_matching_number_in_sorted_list(
                $list,
                $sought
        );

        if ($response == $expected) {
            say "$line; GOT response=$response (as expected)";

            _benchmark_it($expected, $list, $sought);
        } else {
            say "$line; GOT response=$response BUT expected $expected";
            say "value at response IS, $list->[$response]";
            say "value at expected IS, $list->[$expected]";
        }
    }
}

sub _benchmark_it {
    my ($expected, $list, $sought) = @_;
    my $_naive = sub {
        my $best_match_idx = undef;
        my $best_match_diff = SeekMostFit::INF;
        for (my $idx = 0; $idx < scalar @{ $list }; $idx++) {
            my $diff = abs($list->[$idx] - $sought);
            if ($diff < $best_match_diff) {
                $best_match_idx = $idx;
                $best_match_diff = $diff;
            }
        }
        die "Got unexpected result (expected=$expected got $best_match_idx"
            . " during naive search)" if ($best_match_idx != $expected);
    };
    my $_optimized = sub {
        my $response = SeekMostFit::seek_most_matching_number_in_sorted_list(
                $list,
                $sought
        );

        die 'This cannot happen (asserted before)' if $response != $expected;
    };

    cmpthese(
        -1 * SECONDS_BENCHMARKING,
        +{
            '00-naive' => $_naive,
            '01-optimized' => $_optimized
        },
        'auto'
    );
}

_main() unless caller;

1;

__DATA__
initial=0   f=$_                count=1048576               sought=1048574      expected=1048574    mode=integer
initial=1   f=$cur*1.618        count=4096                  sought=12E214       expected=1028       mode=bigfloat
initial=0   f=$_*$_             limit=536870912             sought=6            expected=2

#this series takes forever on my machine to generate:
initial=0   f=$_*$_*$_*$_       limit=9223372036854775808   sought=67           expected=3          mode=integer

# set ts=4 sw=4 et
