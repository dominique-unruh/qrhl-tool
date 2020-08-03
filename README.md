# Binary installation

The binaries require Linux to run.
You can download the binaries [here](https://github.com/dominique-unruh/qrhl-tool/releases). 

## Prerequisites

* Java must be installed (at least Java 9), and the `java` executable must be in the path.
* Emacs must be installed, and the `emacs` executable must be in the path (otherwise edit `proofgeneral.{bat,sh}`).

To check whether this is the case, go into a terminal,
and enter `java` or `emacs`, respectively, and see whether the commands are found.


## Installation

Simply unpack `qrhl.zip`. This will create a directory called `qrhl-0.4`.

To update, simply extract the new version over the old one. (You can
delete the old one first, but then Isabelle will be
redownloaded/recompiled.)

## Executing the demos

In the `qrhl-0.5` directory, execute `proofgeneral.sh`.

This will open emacs running ProofGeneral configured for the qrhl
tool.  Open one of the example files in `examples/`,
e.g. `example.qrhl`.

To step through the examples, use Ctrl-C Ctrl-N to go forward one proof step, Ctrl-C Ctrl-U to go back one.
You will see the current goal and some messages withing the Emacs/ProofGeneral window.
(Or you can use Ctrl-C Ctrl-Return to execute to the cursor position.)
See the [ProofGeneral manual](https://proofgeneral.github.io/doc/userman/) for more information.

Note: The first step of the proof script (`isabelle.`) will take **very long** upon first activation,
because it will download and build Isabelle. 
You need to be online the first time you execute this step. 


## Editing the Isabelle theory files

Some examples depend on an accompanying Isabelle theory. (E.g., 
 `prg-enc-rorcpa.qrhl` depends on the Isabelle theory `PrgEnc.thy`.)
To edit that theory, run Isabelle using the `run-isabelle.{sh,bat}` script.
Then open and edit the file normally.

# Compiling / running from source

* Make sure that `sbt` (Scala Build Tool) is on the path.
* Use `git clone https://github.com/dominique-unruh/qrhl-tool.git` to download the sources.
* Use `git checkout v0.5` (replace `v0.5` by the version you wish to compile, or by `master` for the current development snapshot). 
* Run `./proofgeneral.sh` or `./run-isabelle.sh` as described above (this will (re)compile the sources if needed).
* Run `bin/qrhl` to run the tool on the command line.
* Run `sbt packageBin` to generate the binary `qrhl.zip`.
* Run `sbt test` to run the unit tests.
* You can also open the directory as a project in Intelli/J, but you need to run `sbt assembly` before the first run,
  and after each change of the files in `src/main/isabelle`.
