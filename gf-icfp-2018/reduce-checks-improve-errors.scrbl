#lang gf-icfp-2018

@title{Reducing Tag Checks, Improving Error Messages}

Previous section described naive tag soundness. Great.

Can we reduce the number of checks by
 (1) chaperoning
 (2) using types for escape analysis
 (3) falling back to a last-minute-defense version.


