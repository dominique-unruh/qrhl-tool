[![Build Status](https://travis-ci.com/dominique-unruh/qrhl-tool.svg?branch=master)](https://travis-ci.com/dominique-unruh/qrhl-tool)
[![Gitter chat](https://img.shields.io/badge/gitter-chat-brightgreen.svg)](https://gitter.im/dominique-unruh/qrhl-tool?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

**This describes the installation process for the development snapshot. See [here](https://github.com/dominique-unruh/qrhl-tool/blob/v0.6/README.md) for instructions
for [v0.6](https://github.com/dominique-unruh/qrhl-tool/releases/tag/v0.6).**

# Binary installation

The binaries require Linux, OS/X, or Windows to run.
You can download the binaries [here](https://github.com/dominique-unruh/qrhl-tool/releases).

## Prerequisites

* Java must be installed (at least Java 11), and the `java` executable must be in the path.
* Emacs must be installed, and the `emacs` executable must be in the path (otherwise edit `proofgeneral.{bat,sh}`).
  At least Emacs 26 is required.

To check whether this is the case, go into a terminal,
and enter `java -version` or `emacs -version`, respectively, and see whether the commands are found.

* Isabelle2021 must be installed. Download it at https://isabelle.in.tum.de/website-Isabelle2021/ and 
  unpack it somewhere.
* The AFP must be installed (Isabelle2021 version). Download it at
  https://www.isa-afp.org/download.html and unpack it 
  somewhere.

## Installation

Simply unpack `qrhl.zip`. This will create a directory called `qrhl-snapshot`.

In the `qrhl-snapshot` directory, edit the file `qrhl-tool.conf`: 
Add the configuration keys `isabelle-home = <where you unpackaged Isabelle2021>`
and `afp-home = <where you unpackaged AFP>`.

To update, simply extract the new version.
(But make sure to save your `qrhl-tool.conf`.)

## Executing the demos

In the `qrhl-snapshot` directory, execute `proofgeneral.{sh,bat}`.

This will open emacs running ProofGeneral configured for the qrhl
tool.  Open one of the example files in `examples/`,
e.g. `example.qrhl`.

To step through the examples, use Ctrl-C Ctrl-N to go forward one proof step, Ctrl-C Ctrl-U to go back one.
You will see the current goal and some messages withing the Emacs/ProofGeneral window.
(Or you can use Ctrl-C Ctrl-Return to execute to the cursor position.)
See the [ProofGeneral manual](https://proofgeneral.github.io/doc/userman/) for more information.

Note: The first step of the proof script (`isabelle.`) will take **very long** upon first activation,
because it will build all required Isabelle theories. 

## Editing the Isabelle theory files

Some examples depend on an accompanying Isabelle theory. (E.g., 
 `prg-enc-rorcpa.qrhl` depends on the Isabelle theory `PrgEnc.thy`.)
To edit that theory, run Isabelle using the `run-isabelle.{sh,bat}` script.
Then open and edit the file normally.

# Compiling / running from source

* Make sure that [sbt](https://www.scala-sbt.org/) (Scala Build Tool) is on the path.
* Use `git clone https://github.com/dominique-unruh/qrhl-tool.git` to download the sources.
* Use `git checkout master` (replace `master` by the version/git revision you wish to compile, e.g., `v0.6`). 
* Create a `qrhl-tool.conf` file as described in the binary installation section above.
* Run `./proofgeneral.sh` or `./run-isabelle.sh` as described above (this will (re)compile the sources if needed).
* Run `bin/qrhl` to run the tool on the command line.
* Run `make qrhl.zip` to generate the binary `qrhl.zip`.
* Run `sbt test` to run the unit tests.
* You can also open the directory as a project in [Intelli/J IDEA](https://www.jetbrains.com/idea/), but you should invoke `sbt assembly` before the first time.
