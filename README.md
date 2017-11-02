# Binary installation

The binaries should run on Windows, Linux, and MacOS.
But if you have the choice, Linux should be easiest, especially if Java and Emacs are already installed.
You can download the binaries [here](https://www.ut.ee/~unruh/qrhl.zip). 

On Windows, font problems have been observed (strange characters in the proof state).  

## Prerequisites

* Java must be installed (at least Java 8), and the `java` executable must be in the path.
* Emacs must be installed, and the `emacs` executable must be in the path (or else, edit `proofgeneral.{bat,sh}`).

To check whether this is the case, go into a terminal (or Command Prompt in Windows),
and enter `java` or `emacs`, respectively, and see whether the commands are found.


## Installation

Simply unpack `qrhl.zip`. This will create a directory called `qrhl-0.1alpha`.


## Executing the demos

In the `qrhl-0.1alpha` directory, execute `proofgeneral.sh` (or `proofgeneral.bat` on Windows).
The current directory must be the `qrhl-0.1alpha` directory!

This will open emacs running ProofGeneral configured for the qrhl
tool.  Open one of the example files: `prg-enc-indcpa.qrhl` or
`prg-enc-rorcpa.qrhl`.

To step through the examples, use Ctrl-C Ctrl-N to go forward one proof step, Ctrl-C Ctrl-U to go back one.
You will see the current goal and some messages withing the Emacs/ProofGeneral window.
(Or you can use Ctrl-C Ctrl-Return to execute to the cursor position.)
See the [ProofGeneral manual](https://proofgeneral.github.io/doc/userman/) for more information.

Note: The first step of the proof script (`isabelle auto...`) will take very long upon first activation,
because it will download and build Isabelle. 
You need to be online the first time you execute this step. 


## Editing the Isabelle theory files

The examples `prg-enc-*.qrhl` depend on the Isabelle theory `PrgEnc.thy`.
To edit that theory, run Isabelle using the `run-isabelle.{sh,bat}` script.
Then open and edit the file normally.

# Compiling / running from source

Make sure that `sbt` (Scala Build Tool) is on the path.
Use `git clone git@github.com:dominique-unruh/qrhl-tool.git` to download the sources.
Run `./proofgeneral.sh` or `./run-isabelle.sh` as described above (this will (re)compile the sources if needed).
Run `bin/qrhl` to run the tool on the command line.
Run `sbt packageBin` to generate the binary `qrhl.zip`.
Run `sbt test` to run the unit tests.
You can also open the directory as a project in Intelli/J, but you need to run `sbt assembly` before the first run,
and after each change of the files in `src/main/isabelle`.
