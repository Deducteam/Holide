HOLIDE
======

[![Build Status](https://travis-ci.org/Deducteam/Holide.svg?branch=master)](https://travis-ci.org/Deducteam/Holide)

Holide is an HOL to Dedukti translator. It accepts files in the
OpenTheory article format version 6
(http://www.gilith.com/research/opentheory/article.html) and produces
files for the Dedukti proof checker.

The source code is available online at:
https://github.com/Deducteam/Holide

You need OCaml to compile it. To compile, simply run `make` in the main
directory.

```
Usage: holide <options> <file>

  --just-check   Just check, do not translate
  -o <file>      Set output filename
  --quiet        Suppress all information
  --untyped-def  Use untyped declarations
  --version      Print version and exit
  -help          Display this list of options
  --help         Display this list of options
```

Example
-------

`$HOLIDE_DIR/holide file.art`

This produces a file named `file.dk` which is an encoding of the
theory of the file `file.art`. All generated files depend on the main
HOL logic, which is formalized in the file `dedukti/hol.dk`. To check
it with Dedukti, do:

`dkcheck -I $HOLIDE_DIR/dedukti file.dk`

There are many ways to obtain proofs in the OpenTheory format. If you
have the opentheory tool installed, you can automatically export and
translate some theories of the OpenTheory standard library using `make
stdlib`.

For more information on OpenTheory, visit:
http://www.gilith.com/research/opentheory/

For more information on Dedukti, visit:
https://deducteam.github.io

For feedback or bug reports, please send an email to:
dedukti-dev@inria.fr
