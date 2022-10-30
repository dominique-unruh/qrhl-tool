# Invoking Proof General

Interactively developing proofs using qrhl-tool is done using [Proof General](https://proofgeneral.github.io/).
There are several ways to invoke ProofGeneral with qRHL-support.

[//]: # (Brown text &#40;<font color="brown">like this</font>&#41; applies to the development snapshot only.)

## Invocation script

You can use the invocation script in the qrhl-tool installation directory. 

Steps:
* Make sure `emacs` is in the path. (Running `emacs` in the shell should start emacs.)
* Run `proofgeneral.sh` or `proofgeneral.sh filename.qrhl` in the qrhl-tool installation directory.
  (On Windows: `proofgeneral.ps1`)
* Open files with extension `.qrhl` to edit proofs.

Note: 
* You can add the command-line parameter `-q` to disable loading of your `.emacs` file 
  (Emacs configuration file) if needed.
  (E.g., if your Emacs configuration loads a conflicting version of ProofGeneral.)

Pros:
* No additional installation necessary.

Cons:
* A fresh Emacs instance will be used, you might not like this depending on your preferences. 
* Potential conflicts between your existing Emacs configuration (in the `.emacs` file).
  Use the `-q` option to deactivate loading your `.emacs` file (and thus any preexisting configuration).


## Install Proof General via MELPA

The official distribution of Proof General contains support for qrhl-tool.
You can simply install the most current version via [MELPA](https://melpa.org/).
See the [Proof General installation instructions](https://proofgeneral.github.io/#quick-installation-instructions).
(Other distributions of Proof General may not be up-to-date enough.)

Pros:
* Automatic installation
* Your usual Emacs configuration is used.
* Quite up-to-date. 
  (Only beaten by the [repository version](#repository-version-of-the-qrhl-supporting-proof-general) 
  or the Proof General included in the development snapshot of qrhl-tool.)

Cons:
* Needs to be separately installed (as compared to the [invocation script](#invocation-script)).

## Configure Emacs to use the contributed Proof General

You can configure Emacs to use the Proof General version that comes with qrhl-tool.

Steps:
* Edit your Emacs configuration file (`~/.emacs` on Linux/Mac, for Windows see [here](https://www.gnu.org/software/emacs/manual/html_mono/efaq-w32.html#Location-of-init-file)).
* Add the line `(require 'proof-site "QRHL_TOOL/proofgeneral/proof-general")` to that file.
  Here `QRHL_TOOL` should be replaced by the path to the qrhl-tool installation directory.
* Run `emacs` normally.
* Open files with extension `.qrhl` to edit proofs.

Pros:
* Your usual Emacs configuration is used.

Cons:
* Manual configuration.
* If your system already has Proof General installed, it is not obvious which version Emacs will use.

Optional extra step:
* In Emacs, do `C-0 M-x byte-recompile-directory` and pass the directory `QRHL_TOOL/proofgeneral` when asked. 
  This speeds up loading. Needed only once. Repeat when updating `qrhl-tool`.


## Repository version of the qRHL-supporting Proof General

Similar to the previous solution, only with the most up-to-date version of the qRHL-support.

Steps:
* Clone/download the git repository `https://github.com/dominique-unruh/proofgeneral/tree/qrhl-tool`.
  (Important: make sure to check out the `qrhl-tool` branch.)
* Edit your Emacs configuration file (`~/.emacs` on Linux/Mac, for Windows see [here](https://www.gnu.org/software/emacs/manual/html_mono/efaq-w32.html#Location-of-init-file)).
* Add the line `(require 'proof-site "PROOFGENERAL/generic/proof-site")` to that file.
  Here `PROOFGENERAL` should be replaced by the path to the checked-out repository.
* Run `emacs` normally.
* Open files with extension `.qrhl` to edit proofs.

Pros:
* Your usual Emacs configuration is used.
* Newest possible version of the qRHL-support in Proof General.

Cons:
* Manual configuration.
* If your system already has Proof General installed, it is not obvious which version Emacs will use.

Optional extra step:
* In Emacs, do `C-0 M-x byte-recompile-directory` and pass the directory `PROOFGENERAL` when asked.
  This speeds up loading. Needed only once. Repeat when updating `qrhl-tool`.
