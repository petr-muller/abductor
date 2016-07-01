#!/usr/bin/perl
use FindBin;
use lib "$FindBin::Bin";

# Read the configuration script
use CilConfig;

print "CIL home: $::cilhome\n";
system "cd $::cilhome; make";
