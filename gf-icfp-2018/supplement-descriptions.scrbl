#lang gf-icfp-2018
@require{techreport.rkt}

@title{Benchmark Descriptions}

@bm-desc[
  "sieve"
  "Ben Greenman"
  '()]{
  Computes prime numbers using the sieve of Eratosthenes.
}
@bm-desc[
  "fsm"
  "Linh Chi Nguyen"
  '()]{
  Simulates the interactions of economic agents modeled as finite-state automata.
}
@bm-desc[
  "morsecode"
  "John B. Clements & Neil Van Dyke"
  '()]{
    Computes Levenshtein distances and morse code translations for a fixed
    sequence of pairs of words.
}
@bm-desc[
  "zombie"
  "David Van Horn"
  '()]{
  Implements a game where players avoid enemies.
  The benchmark runs a fixed sequence of moves (representing user input).
}
@bm-desc[
  "suffixtree"
  "Danny Yoo"
  '()]{
    Computes longest common subsequences between strings.
}
@bm-desc[
  "kcfa"
  "Matt Might"
  '()]{
    Performs 1-CFA on a lambda calculus equation built from Church numerals.
}
@bm-desc[
  "snake"
  "David Van Horn"
  '()]{
    Implements the Snake game; the benchmark replays a fixed sequence of moves.
}
@bm-desc[
  "tetris"
  "David Van Horn"
  '()]{
    Replays a pre-recorded game of Tetris.
}
@bm-desc[
  "synth"
  "Vincent St. Amour & Neil Toronto"
  '()]{
  Converts a description of notes and drum beats to @tt{WAV} format.
}

@figure["fig:benchmark-static" "Benchmark Size"
  @exact|{
\setlength{\tabcolsep}{0.2em}\begin{tabular}{lrrr}
Benchmark & \twoline{Untyped}{LOC} & \twoline{Annotation}{LOC} & \# Modules \\[1.5ex]\hline
{\tt sieve} & 35 & 17~~(49\%) & 2 \\[0.3ex]
{\tt fsm} & 182 & 56~~(31\%) & 4 \\[0.3ex]
{\tt morsecode} & 159 & 38~~(24\%) & 4 \\[0.3ex]
{\tt zombie} & 302 & 27~~\hphantom{0}(9\%) & 4 \\[0.3ex]
{\tt jpeg} & 1432 & 165~~{12\\%) & 5 \\[0.3ex]
{\tt suffixtree} & 537 & 129~~(24\%) & 6 \\[0.3ex]
{\tt kcfa} & 229 & 53~~(23\%) & 7 \\[0.3ex]
{\tt snake} & 160 & 51~~(32\%) & 8 \\[0.3ex]
{\tt tetris} & 246 & 107~~(43\%) & 9 \\[0.3ex]
{\tt synth} & 835 & 139~~(17\%) & 10 \\[0.3ex]
\end{tabular}

}|]
