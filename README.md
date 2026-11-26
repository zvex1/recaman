# Recamán's sequence in Lean 4

A machine-checked formalization of Recamán's sequence ([OEIS A005132](https://oeis.org/A005132))
and of **Sloane's conjecture** that every natural number occurs in it, plus an exact fast
simulator used to study how the conjecture could fail or hold.

- Core Lean 4 (v4.36.0) only: no Mathlib, no `sorry`, no `native_decide`.
- Every theorem depends only on Lean's standard axioms `propext`, `Classical.choice` and
  `Quot.sound`. The `#print axioms` audit at the end of `Recaman.lean` prints this on every build.

## Status

`Recaman.SloaneConjecture` is **stated, not proved or disproved**: it is an open problem. This
project proves an exact reformulation and the structural facts that a proof or disproof would have
to work with. The computations below point toward the conjecture being false, but they are
evidence, not a proof.

## Main results (`Recaman.lean`)

| Theorem | What it says |
|---|---|
| `occurs_iff`, `sloane_iff` | `m` occurs ⟺ `m` is among `a 0 … a m`, or `a k = k + m + 1` for some `k`. So the conjecture says the height `a k - k` eventually hits every needed value exactly. |
| `unbounded`, `le_max_succ` | `n + 1 ≤ a n` or `n + 1 ≤ a (n+1)`; the sequence is unbounded. |
| `first_terms`, `not_injective` | The first 25 terms, and `a 20 = a 24 = 42` (kernel computation). |
| `a_mod_two` | Parity law: `a n` is odd iff `n ≡ 1` or `2 (mod 4)`. |
| `exists_back`, `exists_fwd` | Backward steps and forward steps both occur infinitely often. |
| `zigzag`, `zigzag_odd`, `zigzag_below` | After landing on `x` at step `k`, the walk alternates `x, x+k+1, x-1, x+k+2, …`, filling the free run below `x` from the top, as long as its jump tests `x - j - (k+2j+1)` fail. |
| `zigzag_jump` | If the first `j` tests fail and the `j`-th tested number is free, the walk jumps onto it at step `k + 2j + 1`. |
| `entry`, `entry_exposed` | Every backward step either continues a zigzag or is the second of two consecutive backward steps (a *jump*). Late in the sequence, a hole whose upper neighbour is taken can only be entered by a jump. |
| `transition` | When a zigzag's free run runs out at `ℓ`, three forward steps follow and the walk restarts at `2t + (ℓ − 6)`, where `t` is the step number. |
| `cascade`, `cascade_class` | After that transition, the next jump lands exactly `ℓ − 8 − 5j` above the diagonal, and the zigzag that follows scans the numbers just below `ℓ` in residue class `(ℓ + j) mod 3`. So filling one hole sets up the scan for the next hole below it. |
| `ladder_back`, `ladder_transition`, `ladder_zigzag` | Measured against the lines `L·t`, a jump moves one level down and shifts the offset by `−L`; a transition moves two levels up and shifts it by `−(4L + 6)`; a zigzag round shifts it by `−(2L + 1)`. This is why the walk stays on a "ladder" of lines `(L + c)·t` (see below). |
| `window` | If every number strictly between `m` and `m'` (with `m ≡ m' mod 3`) has occurred, then `m` can appear later only via a jump landing exactly `m + 1 + 3j ≤ m' − 2` above the diagonal, followed by a zigzag running down to `m`. |
| `window_suff` | Conversely, such a landing with a long enough free run below it does produce `m`. |
| `window_852655` | Takes Chaffin's data as hypotheses: 852655 and 930058 are the two smallest missing numbers after 10²³⁰ steps. Then 852655 can only appear via a jump landing between 852,656 and 930,056 above the diagonal. |
| `small_occur` | Every `m < 19` occurs within the first 131 terms. |

## Simulator (`sim/recaman_fast.cpp`)

An exact simulation that computes each zigzag in one step from the set of visited numbers,
stored as merged intervals. It applies the rule described by the `zigzag` and `zigzag_jump`
lemmas above; the C++ code itself is tested, not formally verified.

    g++ -O2 -std=c++17 -o recaman_fast recaman_fast.cpp
    ./recaman_fast 1000000000000000 --records    # 10^15 steps, about 40 s and 1.3 GB

Options: `--records` (print each time the smallest missing number changes, with the cascade
behind it), `--stats` (jump landings per decade), `--watch B` (log every zigzag that starts below
`B`), `--sample F` (print the level of one zigzag per factor `F` of time), `--dump A B` (print
every zigzag that starts at a step between `A` and `B`). Values must stay below
2⁶⁴, which limits runs to about 10¹⁸ steps. A 10¹⁸-step run takes about 8 minutes and holds 170
million intervals.

**Validation.** It matches a direct simulation exactly at ten checkpoints up to 10⁹ (the value
`a(N)`, the count of missing numbers below `N`, the number and widths of the holes, and the first
missing numbers). At 10¹⁵ steps it reproduces Wilks's result: the smallest missing number is
852655, followed by 930058 and 930557. At 10¹⁸ steps its 13 smallest missing numbers are exactly
Chaffin's published list at 10²³⁰ steps: 852655, 930058, 930557, 964420, 966052, 966727, 969194,
971330, 971626, 971866, 972275, 972827, 976367.

## What the computations show

**Small numbers are filled by top-down cascades.** Every record fill traced has the same shape.
A jump lands just above the diagonal and its zigzag scans down onto a hole. Draining that hole
restarts the walk at `2t + (ℓ − 6)` (`transition`), and the next scan runs just below `ℓ`
(`cascade`). For example, 1643 was filled at step 3.25·10¹¹. The walk then restarted at
`2t + 1637` and landed at `t + 1635`, and the scan reached 1355.

**The walk lives on a ladder.** At large scales every zigzag starts at about `(L + c)·t` for a
small integer `L` and a common fraction `c`. Jumps lower `L` by 1 and transitions raise it by 2,
and both keep `c` fixed (`ladder_back`, `ladder_transition`). Only zigzag rounds move `c`
(`ladder_zigzag`), so `c` drifts downward and wraps around past 0, four to six times per decade.
The walk can reach the small numbers only while `c` is very close to an integer: then the levels
line up with the diagonal and a cascade can start. `c` moves in steps whose size in absolute terms
grows with `t`, so a pass through 0 usually stops well short of the small numbers.

**Deep cascades are rare, and one nearly reached 852655.** The deep cascades I examined, at
3.3·10¹¹, 3.9·10¹⁴ and 1.47·10¹⁵, each sit exactly on a pass of `c` through 0. Most passes stop
well short, though. Decade 10¹⁵ had six passes, but all six of its landings below 10⁶ came in the
single cascade at 1.47·10¹⁵. Decade 10¹⁶ had no landings below 10⁸ at all. The 3.9·10¹⁴ cascade
was one unbroken run of about 8,000 zigzags on the `c = 0` ladder that ate holes down to 2406.

The 9·10¹⁷ cascade ate its way down from 9.9 million to 963744, the last hole ≡ 0 (mod 3) below
10⁶. After draining 963744, the transition's very first jump test succeeded (`j = 0`), so the
next scan ran in residue class `(963744 + 0) mod 3 = 0`. That class was then empty: the zigzag
found nothing in a free run of 234 billion rounds, and the cascade died. With `j = 1` the scan
would have been in class 1, and by `cascade` it would have run down onto 930058, one class-1 scan
away from 852655.

**The small numbers are freezing.** Missing numbers below 10⁶: 1,313 at 10¹², 221 at 10¹⁵, 14 at
10¹⁶ and 13 at 10¹⁸, with 852655 at the bottom. Jump landings on numbers below 10⁷ per decade:
391 (decade 10⁹), 246, 214, 125, 79, 115, 13, 0 (decade 10¹⁶), then 84 (one cascade, decade
10¹⁷). Chaffin's list shows the 13 holes left below 976368 at 10¹⁸ all still there at 10²³⁰. If
deep cascades keep thinning out like this, only finitely many more small numbers will ever be
filled. Infinitely many numbers would then never appear, which would make the conjecture false.
Proving that, though, means controlling these near-integer passes of `c` forever, and no known
method does.

## Further reading

See `LITERATURE_AND_FINDINGS.md` for the literature review and which parts of this work were
already known, and `PROOF_PLAN.md` for the plan of attack on a formal proof. `data/` holds
Chaffin's lists of holes below 2³² and of all landings up to 10⁶¹².

## Build

With [elan](https://github.com/leanprover/elan) installed, run `lake build`.
Alternatively, with Lean 4.36.0 on your `PATH`, run `lean Recaman.lean`.
