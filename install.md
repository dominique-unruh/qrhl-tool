
# Binary installation

Qrhl-tool requires Linux, OS/X, or Windows to run.

You can download the qrhl-tool binaries [here](https://github.com/dominique-unruh/qrhl-tool/releases).

The binary development snapshot can be downloaded from [here](https://nightly.link/dominique-unruh/qrhl-tool/workflows/test/master/qrhl.zip).

On Linux, you can also use the interactive installer to install release or development snapshot. Using the following command line:
```shell
wget -nv https://github.com/dominique-unruh/qrhl-tool/raw/master/installer.py -O /tmp/installer.py && python3 /tmp/installer.py
```
This will download qrhl-tool and install the prerequisites as well, except Java and Emacs.
Use `sudo python3` instead of `python3` if you want to install files outside your home directory.

## Prerequisites

* Java must be installed (at least Java 11), and the `java` executable must be in the path.
* Emacs must be installed, and the `emacs` executable must be in the path (otherwise edit `proofgeneral.sh`).
  At least Emacs 25 is required.

To check whether this is the case, go into a terminal,
and enter `java -version` or `emacs -version`, respectively, and see whether the commands are found.

* [Isabelle2021-1](https://isabelle.in.tum.de/website-Isabelle2021-1/) must be installed.
  Simply download it and unpack it somewhere.
* The AFP (version 2021-1) must be installed. Download it at https://www.isa-afp.org/download.html, respectively, and unpack it 
  somewhere.

## Installation

Simply unpack `qrhl.zip`. This will create a directory called `qrhl-0.7`.
(Or `qrhl-snapshot` in case of the development snapshot.)

Edit `.qrhl-tool.conf` in your home directory.
Add the configuration keys `isabelle-home = <where you unpackaged Isabelle>`
and `afp-home = <where you unpackaged AFP>`.
(See `qrhl-tool.conf.sample` in the distribution directory.)

To update, simply extract the new version.
(Possibly updating `.qrhl-tool.conf` if the Isabelle version has changed.)

## Executing the demos

In the `qrhl-0.7` directory, execute `proofgeneral.sh`.

This will open emacs running ProofGeneral configured for the qrhl
tool.  Open one of the example files in `examples/`,
e.g. `example.qrhl`.

(See _[invoking ProofGeneral](proofgeneral.md)_ for alternative ways, or if you use Windows.)

To step through the examples, use Ctrl-C Ctrl-N to go forward one proof step, Ctrl-C Ctrl-U to go back one.
You will see the current goal and some messages withing the Emacs/ProofGeneral window.
(Or you can use Ctrl-C Ctrl-Return to execute to the cursor position.)
See the [ProofGeneral manual](https://proofgeneral.github.io/doc/userman/) for more information.

Note: The first step of the proof script (`isabelle.`) will take **very long** upon first activation,
because it will build all required Isabelle theories. 
Do not start other instances of Isabelle or the tool while this is in progress.

## Editing the Isabelle theory files

Some examples depend on an accompanying Isabelle theory. (E.g., 
 `prg-enc-rorcpa.qrhl` depends on the Isabelle theory `PrgEnc.thy`.)
To edit that theory, run Isabelle using the `run-isabelle.{sh,bat}` script.
Then open and edit the file normally.

# Compiling / running from source

* Make sure that [sbt](https://www.scala-sbt.org/) (Scala Build Tool) is on the path.
* Use `git clone https://github.com/dominique-unruh/qrhl-tool.git` to download the sources.
* Use `git checkout master` (replace `master` by the version/git revision you wish to compile, e.g., `v0.7`). 
* Create a `qrhl-tool.conf` file as described in the binary installation section above.
* Run `./proofgeneral.sh` or `./run-isabelle.sh` as described above (this will (re)compile the sources if needed).
* Run `bin/qrhl` to run the tool on the command line.
* Run `make qrhl.zip` to generate the binary `qrhl.zip`.
* Run `sbt test` to run the unit tests.
* You can also open the directory as a project in [Intelli/J IDEA](https://www.jetbrains.com/idea/), but you should invoke `sbt assembly` before the first time.
