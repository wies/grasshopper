<img align="right" width="300" src="logo.png"/>

GRASShopper
=======
![Version 0.6 pre](https://img.shields.io/badge/version-0.6_pre-green.svg)
[![BSD licensed](https://img.shields.io/badge/license-BSD-blue.svg)](https://raw.githubusercontent.com/wies/grasshopper/master/LICENSE)
[![Build Status](https://travis-ci.org/wies/grasshopper.svg?branch=master)](https://travis-ci.org/wies/grasshopper)

GRASShopper is an experimental verification tool for programs that
manipulate dynamically allocated data structures. GRASShopper programs
can be annotated with specifications expressed in a decidable
specification logic to check functional correctness properties. The
logic supports mixing of separation logic and first-order logic
assertions, yielding expressive yet concise specifications.

The tool is released under a BSD license, see file LICENSE for
details.


Installation Requirements
-------------------------
- OCaml, version >= 4.07

- OCaml Findlib, version >= 1.6.2

- Z3, version >= 4.5, and/or

- CVC4, version >= 1.5

GRASShopper has been tested on Linux, Mac OS, and Windows/Cygwin.

The easiest way to satisfy all OCaml-related installation requirements
is to install the OCaml package manager OPAM and then execute the
following commands
```bash
opam switch 4.07.0
opam install -y ocamlfind
opam install -y ocamlbuild
eval $(opam config env)
```

To run the tests (see below) you will also need the `gtime, gdate` commands,
which can be installed in Mac OS using homebrew (`brew install coreutils`).

Installation Instructions 
-------------------------
- To produce native code compiled executables, run 
```bash
./build.sh
```

- Optional: to check whether the build succeeded, run
```bash
./build.sh tests
```

Usage
-------------------------

To run GRASShopper, execute e.g.
```bash
./grasshopper.native tests/spl/sl/sl_reverse.spl
```
The analyzer expects the Z3 (respectively, CVC4) executable in the path.

To see the available command line options, run
```bash
./grasshopper.native -help
```

Emacs Major Mode
-------------------------

GRASShopper provides an Emacs major mode for GRASShopper programs.
The mode provides syntax highlighting and automatic indentation for
the GRASShopper input programs (see tests/spl for examples).

To use the Emacs mode, copy the files in the directory emacs-mode to
your site-lisp directory and add the following line to your `.emacs`
file:

```elisp
(load "spl-mode")
```

Optional: Flycheck minor mode

If you are using Emacs 24.1 or newer, we suggest to use the
flycheck minor mode of the SPL emacs mode. To do so, copy the file
emacs-mode/flycheck.el into your `site-lisp` directory. Additionally,
you need to put the GRASShopper executable in your path and rename it
to `grasshopper`. The mode supports on-the-fly syntax and type
checking of SPL programs and provides keyboard shortcuts for verifying
the program from inside buffers. See the documentation in the file
`spl-mode.el` for details.

Note that we are using a patched version of the original flycheck mode
by Sebastian Wiesner. The minor mode will not work correctly with the
original version of the flycheck mode.

For more information visit http://cs.nyu.edu/wies/software/grasshopper
