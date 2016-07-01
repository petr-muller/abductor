Abductor 1.0: a prototype compositional analyser for C programs, based on separation logic. 

 * Copyright (c) 2007-2009, 
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk> 
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk> 
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 * All rights reserved.
 

CONTENTS OF THIS FILE
  (1) Remarks on usage and other general comments
  (2) License information

---------REMARKS ON USAGE, OTHER COMMENTS-------------------------------


SYSTEM REQUIREMENTS
An x86 machine running Mac, linux, or Windows.

TO COMPILE ABDUCTOR:

go to the directory cil and run

./configure
make


----------
TO RUN ABDUCTOR on a single file:

  abductor file.c

where file.c is a C file that compiles correctly.
 
As an example, running

../cil/bin/abductor recursive_loops_small.c

from directory 

benchmarks 
 
analyses the file recursive_loops_small.c. This generates a number
of pre/post specs which you can see on the standard output.
It also generates several ".dot" files, which allow you
to view a pictorial representation of the specs, using a viewer
such as graphvis. If you view delete_nested_list_1.dot you see a spec
for that procedure. To see the effect of changing a procedure
you might comment out lines 49 and 50 of recursive_loops_small.c,
run abductor again, and see the different spec generated (since the footprint of delete_nested_list changes).


TO RUN ABDUCTOR on a project:

AbductorMultiFile command 

where command can be

Commands:
  unpack	      unpack files (e.g. sources.tar.gz)
  clean		 delete unpacked files
  configure	 execute configure script
  test [n]	      execute test using n jobs
  retest [n]	 re-execute test incrementally using n jobs

AbductorMultiFile works for projects that are build with gnu makefiles.
Command unpack can be used to unpack a tar.gz tarball containing the sources. Command configure will run the configure script of the project.
Command test will run the abductor analysis. Command re-test will re-run the analysis in a incremental mode, i.e., analysing only the files that have been changed since the last analysis. Command clean erase unpacked files of the project.

As an example, let's analyse the imap benchmark provided with the distribution. In the  cyrus-imapd-2.3.13 directory there is a tarball with the sources. We can analyse this project with the following steps:

1) go inside the cyrus_imap directory

 cd benchmarks/cyrus-imapd-2.3.13/

2) unpack the tar ball with

 ../../cil/bin/AbductorMultiFile unpack

3) you have to configure the project. The following sequence
did the trick forMacOS X on running on an Intel Core 2 Duo

cd cyrus-imapd-2.3.13
./configure CC=/usr/bin/gcc-4.0 --with-bdb=/usr/local/BerkeleyDB.4.7/
cd ..
 
Sometimes, ./configure on its own will work for the second line. For some projects  ../../cil/bin/AbductorMultiFile will work. For other projects than imap, try these simpler options first. We leave configuration 
for you to work out on a case by case basis. 

4) run the analysis (from directory benchmarks/cyrus-imapd-2.3.13)

 ../../cil/bin/AbductorMultiFile test
 
This can take a little while.
 
5) If you want to look yourself at the output, you can poke around the directory db_cyrus-imapd-2.3.13_j1. We can see a summary of the results by giving the following command:

../../cil/bin/stats.pl db_cyrus-imapd-2.3.13_j1/
 
You can do this while the analysis is running: it will give you a picture of the results so far.

6) Amongst the memory leaks is one at line 709 of 
   cyrus-imapd-2.3.13/lib/charset.c
Have a look and fix that leak. You might look in the surrounding area
at other return statements for a hint on how to fix.
 
7) Rerun abductor after you have fixed the leak by issuing the command

../../cil/bin/AbductorMultiFile retest
 
retest exercises the incremental aspect of abductor: this run will be 
much quicker than the first one.
 
8) Look at the summary again 
../../cil/bin/stats.pl db_cyrus-imapd-2.3.13_j1/
Hopefully the number of (potential) leaks has changed!
 
sendmail and openssl projects are also included. 
 

 
ACKNOWLEDGEMENTS.
The research on Abductor has been supported by a number of EPSRC research grants, including Advanced Fellowships for Calcagno, Yang and O'Hearn, and an RAEng/EPSRC Research Fellowship for Distefano. O'Hearn acknowledges the support of a Royal Society Wolfson Research Merit Award.
 
Some of the theoretical work underpinning Abductor was done jointly with Josh Berdine, Byron Cook, Oukseh Lee and Thomas Wies. 

Abductor uses the CIL compiler infrastructure, and the CIL License is duly reproduced below, as required by the authors of CIL. 

SpaceInvader is implemented in the OCaml programming language.
 
----------ABDUCTOR LICENSE AND WARRANTY DISCLAIMER------------
* Copyright (c) 2007-2009, 
 *  Cristiano Calcagno    <ccris@doc.ic.ac.uk> 
 *  Dino Distefano        <ddino@dcs.qmul.ac.uk> 
 *  Hongseok Yang         <hyang@dcs.qmul.ac.uk>
 *  Peter O'Hearn         <ohearn@dcs.qmul.ac.uk>
 * All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, 
this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, 
this list of conditions and the following disclaimer in the documentation 
and/or other materials provided with the distribution.

3. The names of the contributors may not be used to endorse or promote products 
derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" 
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE 
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF 
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
POSSIBILITY OF SUCH DAMAGE.



------CIL License----------------------

Copyright (c) 2001-2007,

George C. Necula <necula@cs.berkeley.edu>
Scott McPeak <smcpeak@cs.berkeley.edu>
Wes Weimer <weimer@cs.berkeley.edu>
Ben Liblit <liblit@cs.wisc.edu>
Matt Harren <matth@cs.berkeley.edu>
All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, 
this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, 
this list of conditions and the following disclaimer in the documentation 
and/or other materials provided with the distribution.

3. The names of the contributors may not be used to endorse or promote products 
derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" 
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE 
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF 
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
POSSIBILITY OF SUCH DAMAGE.


