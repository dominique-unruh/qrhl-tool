# Invoking proofgeneral

Interactively developing proofs using qrhl-tool is done using [ProofGeneral](https://proofgeneral.github.io/).
There are several ways to invoke ProofGeneral with qRHL-support.

## Invocation script

If you are using Linux or Mac, you can use the invocation script in the qrhl-tool installation directory. 

Steps:
* Make sure `emacs` is in the path. (Running `emacs` in the shell should start emacs.)
* Run `proofgeneral.sh` or `proofgeneral.sh filename.qrhl` in the qrhl-tool installation directory.
* Open files with extension `.qrhl` to edit proofs.

Pros:
* No additional installation necessary.

Cons:
* A bare-bones Emacs is used without any of your personal configuration.
  (If you don't usually use Emacs, this should not matter.)

## Configure Emacs to use the contributed ProofGeneral

You can configure Emacs to use the ProofGeneral version that comes with qrhl-tool.

Steps:
* Edit your Emacs configuration file (`~/.emacs` on Linux/Mac, for Windows see [here](https://www.gnu.org/software/emacs/manual/html_mono/efaq-w32.html#Location-of-init-file)).
* Add the line `(require 'proof-site "QRHL_TOOL/proofgeneral/generic/proof-site")` to that file.
  Here `QRHL_TOOL` should be replaced by the path to the qrhl-tool installation directory.
* Run `emacs` normally.
* Open files with extension `.qrhl` to edit proofs.

Pros:
* Your usual Emacs configuration is used.

Cons:
* Manual configuration.
* If your system already has ProofGeneral installed, it is not obvious which version Emacs will use.

## Repository version of the qRHL-supporting ProofGeneral

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
* Newest possible version of the qRHL-support in ProofGeneral.

Cons:
* Manual configuration.
* If your system already has ProofGeneral installed, it is not obvious which version Emacs will use.

## Use the MELPA version of ProofGeneral

Not supported yet. Support is [upcoming](https://github.com/ProofGeneral/PG/pull/636).
