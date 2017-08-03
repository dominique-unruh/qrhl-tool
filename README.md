= Binary installation

The binaries should run on Windows, Linux, and MacOS.
But if you have the choice, Linux should be easiest, especially if java and emacs are already installed.

== Prerequisites

* Java must be installed (at least Java 8), and the java executable must be in the path.
* Emacs must be installed, and the emacs executable must be in the path (or else, edit proofgeneral.{bat,sh}).

To check whether this is the case, go into a terminal (or Command Prompt in Windows),
and enter java or emacs, respectively, and see whether the commands are found.


== Installation

Simply unpack qrhl.zip. This will create a directory called qrhl-0.1.

== Executing the demos

In the qrhl-0.1 directory, execute proofgeneral.sh (or proofgeneral.bat on Windows).
The current directory must be the qrhl-0.1 directory!

This will open emacs running ProofGeneral configured for the qrhl
tool.  Open one of the example files: prg-enc-indcpa.qrhl,
prg-enc-rorcpa.qrhl, or teleport.qrhl.

To step through the examples, use Ctrl-C Ctrl-N to go forward one proof step, Ctrl-C Ctrl-U to go back one.
You will see the current goal and some messages withing the Emacs/ProofGeneral window.
(Or you can use Ctrl-C Ctrl-Return to execute to the cursor position.)
See the ProofGeneral manual for more information.

Note: The first step of the proof script ("isabelle ...") will take very long upon first activation,
because it will download and install Isabelle.

== Editing the Isabelle theory files

