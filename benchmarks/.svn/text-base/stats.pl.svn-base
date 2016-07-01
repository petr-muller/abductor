#!/usr/bin/perl

######################################################
# Copyright (c) 2006-2008,                           #
#  Cristiano Calcagno    <ccris@doc.ic.ac.uk>        #
#  Dino Distefano        <ddino@dcs.qmul.ac.uk>      #
#  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>     #
#  Hongseok Yang         <hyang@dcs.qmul.ac.uk>      #
# All rights reserved.                               #
######################################################

my $loc = 0;
my $num_procs = 0;
my $num_files = 0;
my $ok = 0;
my $ok_pc = 0;
my $timeouts = 0;
my $timeouts_pc = 0;
my $exceptions = 0;
my $time = 0.0;
my $specs = 0;
my $failures = 0;
my $leaks = 0;

if ($#ARGV < 0) {
  print "No arguments passed\n";
  exit;
}

$dir = $ARGV[0];
@files = <${dir}/*.stats>;
foreach $file (@files) {
  open(DAT,$file);
  my @lines = <DAT>;
  close(DAT);

  foreach $_ (@lines) {
    if(/\+ FILE:(.*) (LOC:)(.*)COVERAGE:(.*)\/(.*)/) {
      $visited_nodes += $4;
      $total_nodes += $5;
      $loc += $3;
      $num_files += 1;
    }
    elsif(/\+  num_procs:(.*)\((.*)ok,(.*)timeouts,(.*)exceptions\)/) {
      $num_procs += $1;
      $ok += $2;
      $timeouts += $3;
      $exceptions += $4;
    }
    elsif(/\+  time:(.*)/) {
      $time += $1;
    }
    elsif(/\+  specs:(.*)/) {
      $specs += $1;
    }
    elsif(/\+  failures:(.*)/) {
      $failures += $1;
    }
    elsif(/\+  exceptions:(.*)/) {
      @exceptions = split(/\s+/, $1);
      foreach $_ (@exceptions) {
	if(/(.*):(.*)/) {
	  $excep_type{$1}+=$2;
	}
      }
    }
  }
}


# compute percentage
$ok_pc=$ok * 100 / $num_procs;
$timeouts_pc=$timeouts * 100 / $num_procs;
$coverage = $visited_nodes * 100 / $total_nodes;

printf "\nTOTAL num_files: $num_files,  LOC: $loc,  TIME: $time,  SPECS: $specs, FAILURES: $failures, COVERAGE: %2.1f%", $coverage;
printf "\n  num_procs: $num_procs";
printf "\n  ok: %d  (%2.1f%%)", $ok , $ok_pc;
printf "\n  timeouts: %d  (%2.1f%%)", $timeouts, $timeouts_pc;
printf "\n  exceptions: %d", $exceptions; 
while (($excep_name, $excep_val) = each(%excep_type))
{
    $perc_e=$excep_val * 100 / $exceptions;
    printf "\n     - %s: %d  (%2.1f%% of excep.)", $excep_name, $excep_val,  $perc_e;
}
printf "\n";
