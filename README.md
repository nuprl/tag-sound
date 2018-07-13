icfp-2018
===

This folder contains an artifact for "A Spectrum of Soundness and Performance".


Instructions for Reviewers
---

1. Run `git status`, check that:
   - the current branch is `icfp-2018`
   - there is an untracked folder `output`
   - there are no other untracked files or folders
2. Run `make` (expected time: 1 hour)
3. Check that:
   - the Makefile finished successfully
   - the paper built --- the following 2 files should match:
     * `gf-icfp-2018/gf-icfp-2018.pdf`
     * `output/gf-icfp-2018.pdf`
   - the supplement built --- these files should match:
     * `gf-icfp-2018/gf-icfp-2018-supplement.pdf`
     * `output/gf-icfp-2018-supplement.pdf`
   - the sample benchmarks ran successfully --- these files should match:
     * `sample-data.png`
     * `output/sample-data.png`
4. Check that the plots in `sample-data.png` match the plots for `morsecode`
   and `zombie` in Section 3 of `gf-icfp-2018/gf-icfp-2018.pdf`

Optionally:

1. Check that the supplement contains proofs of the major theorems
   in the paper
2. Open `example.rkt`, make changes to the code, try to find bugs in
   the `#:locally-defensive` prototype. (Run with `./racket example.rkt`.)
3. Check that the redex models in `gf-icfp-2018/model-design/` look
   something like the models in the paper.
4. Re-run all the benchmark results (expected time: 100 hours)
   - `make new-data`
   - `./racket src/plot-sample-data.rkt sample-data/XXX` where `XXX` is the
      name of the folder created by `make new-data`


What does `make` do?
---

Running `make`:

- installs a local copy of Racket v6.10.1 (if not already installed)
- rebuilds the paper and supplement
- runs a small file to test the implementation
- runs unit tests for our redex models (in `gf-icfp-2018/model-design/`
- collects data for 2 benchmarks: `morsecode` and `zombie`
- plots the data for the 2 benchmarks


What's in this repository?
---

An example file:

- `example.rkt` simple test for TR_N and TR_LD


Source for the paper:

- `gf-icfp-2018/` source code for the paper and supplement
- `benchmarks/` source code for the benchmark programs. Each benchmark has 2
  copies: one for TR_N (natural embedding, aka standard Typed Racket)
  and one for TR_LD (locally-defensive embedding, our prototype)
- `data/` benchmark results that we collected while preparing the submission


A local copy of Racket v6.10.1 with our extended version of Typed Racket:

- `src/` see `src/README.md` to learn more


Links to executables for the copy of Racket v6.10.1:

- `drracket` an IDE
- `racket` runs Racket, via `./racket FILENAME`
- `raco` the Racket command-line tool, used by the Makefile


Other things:

- `README.md` this file
- `Makefile`
- `output/` results from a previous run of `make all` on this VM


Notes
---

The username for this VM is `vagrant` and the password is `vagrant`

Make sure to access this VM with port forwarding.
If you have the VM unpacked and running in VirtualBox the command to connect
 with port forwarding is: `ssh -Y -p2222 vagrant@127.0.0.1`

To view PDF files, use `evince FILE.pdf`

To view PNG files, use `eog FILE.png`

Source for this artifact: <https://github.com/nuprl/tag-sound>
