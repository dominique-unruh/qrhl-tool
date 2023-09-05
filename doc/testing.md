# Testing / continuous integration

This file is more of a personal collection of notes but can be fleshed out on demand.

## Setting up new Isabelle distro for testing

* Get the binary link and the AFP link (https://isabelle-dev.sketis.net/phame/post/view/58/release_candidates_for_isabelle2022/)
* Locally:
  * Update AFP (if RC):
    * In `~/r/afp`: `git fetch mirror-afp-devel master:afp-devel`
    * `git checkout afp-devel`
    * `git push`
    * Identify git revision for correct AFP version (compare log of AFP repo link and `git log`)
    * `git checkout REVISION`
    * `git tag for-IsabelleVERSION`
    * `git push`
  * Isabelle -> `/opt` or `c:\Programs`
    * `sudo chown -R unruh /opt/IsabelleVERSION` (Linux)
    * In `.../IsabelleVERSION/etc/options`: `option system_heaps : bool = true`
* Login to Linux test server (SSH)
  * Isabelle -> `/opt`
  * AFP -> `/opt` (named `afp-VERSION`)
* Login to OS/X test server (SSH)
  * Isabelle -> `~`
  * AFP -> `~` (named `afp-VERSION`)
  * Add `ML_OPTIONS="--maxheap 2G"` in `~/.isabelle/Isabelle2022-RC2/etc/settings`
  * In `.../IsabelleXXX.app/etc/options`, set `timeout_scale` to `10`.
* Login to Windows test server (GUI)
    * Isabelle -> `c:\`
    * AFP -> `c:\` (named `afp-VERSION`)
* In scala-isabelle (locally):
  * Replace `2022-RC2` (or whatever previous version) mentions by `2022-RC3` (or whatever)
  * Run tests (in IDEA)
  * Commit with message `Enabled IsabelleVERSION.`
  * `git push`
  * Check CI results (https://github.com/dominique-unruh/scala-isabelle/actions/)
* In qrhl-tool (locally):
  * Checkout branch for next Isabelle version (e.g., `isabelle2022`)
  * `git pull`
  * `git fetch origin master`
  * `git merge master`
  * Replace `2022-RC2` (or whatever previous version) mentions by `2022-RC3` (or whatever)
    in file `isabelleVersion`
  * `sbt createIsabelleNames`
  * Update `/home/unruh/.qrhl-tool.conf` as well
  * Run tests (in IDEA)
  * Commit with message `Updated to IsabelleVERSION.`
  * `git push`
  * Check CI results (https://github.com/dominique-unruh/qrhl-tool/actions/)
* In `pq-fo-verify` (locally):
  * `git checkout master` 
  * `git pull`
  * `./test.sh`
