# Recamán's sequence: literature review and findings so far

Status as of 26 November 2026. Written as a handoff for the next phase: attacking a formal proof
or disproof of Sloane's conjecture.

## 1. The problem

`a(0) = 0`; `a(n) = a(n-1) - n` if that is positive and not already in the sequence, otherwise
`a(n-1) + n` (OEIS [A005132](https://oeis.org/A005132)). **Sloane's conjecture** (1991): every
non-negative integer appears. Formalized as `Recaman.SloaneConjecture` in `Recaman.lean`.

## 2. Literature review

### What is proved

Nothing substantial. No paper, preprint or formal development proves or disproves the
conjecture, or any non-trivial partial result about which numbers appear. Every source below
calls the question open:

- **Myers, Schroeppel, Shannon, Sloane, Zimmermann (and Alekseyev in v2), "Three Cousins of
  Recamán's Sequence"**, [arXiv:2004.14000](https://arxiv.org/abs/2004.14000), 2020/2021,
  *Fibonacci Quarterly* 60(3). Introduction: "The most basic question about this sequence is
  still unanswered: does every nonnegative integer appear? … Thirty years ago it seemed like a
  very plausible conjecture that every number would eventually appear. Today, it is not so
  clear." The paper itself is about three *different* sequences (sum, product and concatenation
  analogues) and proves results only for those. It offers no technique aimed at Recamán.
- **Sloane, "A Handbook of Integer Sequences Fifty Years Later"**,
  [arXiv:2301.03149](https://arxiv.org/abs/2301.03149), 2023, pp. 10, 12–13. Lists it as open.
- **Sloane, comment in A005132** (Feb 26 2017): "That was written in 1991. Today I'm not so sure
  that every number appears."
- **Korssjoen, Li, Steinerberger, Tripathi, Zhang, "Finding structure in sequences of real
  numbers via graph theory: a problem list"**, [arXiv:2012.04625](https://arxiv.org/abs/2012.04625),
  2020, §2.9. Empirical observations of hidden structure; explicitly open problems.
- **Sloane, "My favorite integer sequences"** (SETA '98) and **"Seven Staggering Sequences"**
  ([arXiv:0912.2394](https://arxiv.org/abs/0912.2394)): expository.
- **Chaffin, Rains, Sloane, Wilks, "Numerical investigations of Recamán's sequence"**: cited as
  "in preparation" since about 2018. I found no preprint.
- A web search for 2023–2026 papers found no claimed proof. I also found no formal
  (Lean/Coq/Isabelle) work on this sequence. As far as I can tell, `Recaman.lean` is the first.

Recamán-like sequences with genuine theorems exist, but none of their techniques transfer.
Examples are A171884, the lexicographically earliest *injective* walk with `|a(n+1)-a(n)| = n`,
and the cousins above.

### What is known computationally

| Who | Reach | Result |
|---|---|---|
| Bell Labs group (Sloane, Wilks, Rains, …), 2001 | 10¹⁵ terms | Every number below 852655 appears; 852655 missing. Introduced the speed-up. |
| Chaffin, 2018 | 10²³⁰ | 852655 still missing; first 13 missing numbers listed (A005132 comment). |
| Chaffin, Feb 2026, ["Computing the Recamán Sequence"](https://benchaffin.com/recaman/recaman.html) | 10⁶¹² | 852655 still missing. 14 months on a 256 GB machine with a 30 TB disk array; stopped by his 2048-bit number size, not by disk. |

Chaffin's 2026 page is the most important single source. Its contents:

- **Algorithm.** "Ping-pong" sections, our zigzags, computed in one step. A section ends when
  the lower range hits a taken number, or when a hole "a multiple of 3 steps away" lets the walk
  subtract twice. That second case is our jump test. Visited numbers are stored as ranges in a
  red-black tree of range arrays, paged to disk. This is the same algorithm as
  `sim/recaman_fast.cpp`, minus the paging and bignums.
- **The `a(n) mod n` picture.** "Terms can only be small relative to n when (a(n) mod n) is
  small … The value of (a(n) mod n) stays the same or decreases from one term to the next, until
  it wraps around." The smallest term between wraps is a **landing**. This is exactly our ladder
  fraction `c`, since `c·n = a(n) mod n`. New OEIS entries: A393814/A393815 (landing values and
  indices), A065052 (`a(n) mod n`), A390717/A392407 (records of consecutive additions and
  subtractions), A064292/A064290 (height).
- **Near misses.** "The lowest it goes after hitting 2406 is a(899989616955022684) = 963744. The
  most dramatic is around term 10⁴¹, at a(177900612666336352118510768792480139301821) = 2023155.
  After that, the lowest it gets is about 10²⁷, around term 10¹⁶⁷." His 963744 index is exactly the
  step our replay found.
- **Data**, copied into `data/`:
  - `rec-holes-2_32.txt`: all 3,102 missing numbers below 2³² after 10⁶¹² terms. SHA-256
    `11ee84c1…6f6aa`.
  - `rec-landings-1e612.txt`: all 5,104 landings up to 10⁶¹². SHA-256 `2fa54109…a3c83`.
- **Correctness.** Cross-checked across program versions. The first 10²³⁰ terms were run
  several times; the final stretch to 10⁶¹² only once.

Statistics I computed from his landings file:
- About **8.4 landings per decade** on average between 10¹⁰⁰ and 10⁶⁰⁰. Over 10⁹–10¹⁵ his counts
  per decade (4, 4, 5, 4, 5, 6, 6) match my independent count of passes of `c` through 0 exactly.
- Landings get relatively shallower: the median of log(value)/log(step) after 10¹⁰⁰ is 0.977.
  Of 4,752 landings after 10⁵⁰, only 3 go below √step.
- The only landings below 10⁸ after step 10¹⁵ are 964419 and 79504751 (both around
  1.47·10¹⁵), 48708718, 48621489 and 963744 (all around 9·10¹⁷), and 2023155 (around 10⁴¹).

### What this means for our work

Several things I presented earlier as findings are **already known**, at least in substance:
- the zigzag-skipping algorithm;
- the every-third-number jump test;
- the `a(n) mod n` drift and wraparound (the ladder fraction);
- landings as the only chances to fill small holes;
- the 963744 near miss at a(899989616955022684).

As far as I can find, three things are **not** in the literature:
- the formal proofs in `Recaman.lean`;
- the exact transition and cascade formulas: restart at `2t + (ℓ − 6)`, next landing
  `ℓ − 8 − 5j` above the diagonal, scan class `(ℓ + j) mod 3`;
- the explanation of why the 963744 near miss stopped (the residue class it scanned was empty).

## 3. Our findings so far

### Machine-checked (`Recaman.lean`, Lean 4.36, core only, no `sorry`)

- **Reformulation** (`occurs_iff`, `sloane_iff`): `m` appears ⟺ `m ∈ {a 0..a m}` or
  `a k = k + m + 1` for some `k`.
- **Basic facts:** unbounded; not injective (`a 20 = a 24 = 42`); parity law
  (`a n` odd ⟺ `n ≡ 1, 2 mod 4`); infinitely many backward and forward steps.
- **Dynamics:**
  - `zigzag`, `zigzag_odd`, `zigzag_below`, `zigzag_jump`: the ping-pong section and how it ends.
  - `entry`, `entry_exposed`: late in the sequence, holes can only be entered by two consecutive
    backward steps.
  - `transition`: after a run is used up at `ℓ`, the walk restarts at `2t + (ℓ − 6)`.
  - `cascade`, `cascade_class`: the next landing is `ℓ − 8 − 5j` above the diagonal, in residue
    class `(ℓ + j) mod 3`.
  - `ladder_back`, `ladder_transition`, `ladder_zigzag`: exact offset bookkeeping relative to
    lines `L·t`.
- **Window theorem** (`window`, `window_suff`, `window_852655`): if everything strictly between
  `m` and `m'` (same residue mod 3) has occurred, then `m` appears later **iff** a jump lands
  exactly `m + 1 + 3j ≤ m' − 2` above the diagonal and the zigzag after it runs down to `m`. With
  Chaffin's data as hypotheses, 852655 can appear only via a landing between 852,656 and 930,056
  above the diagonal.

### Computational (`sim/recaman_fast.cpp`; tested, not formally verified)

- It matches the direct simulation exactly at ten checkpoints up to 10⁹. It reproduces Wilks's
  852655 at 10¹⁵. At 10¹⁸ its first 20 missing numbers equal Chaffin's list at 10⁶¹².
- **Cascades.** Small holes are filled top-down during a landing: drain a hole, restart at
  `2t + ℓ − 6`, land just below `ℓ`, repeat. Example: the 3.9·10¹⁴ cascade, an unbroken run of
  about 8,000 zigzags that ate holes down to 2406.
- **Freezing.** Missing numbers below 10⁶: 1,313 at 10¹², 221 at 10¹⁵, 14 at 10¹⁶, 13 at 10¹⁸.
  All 13 are still missing at 10⁶¹².
- **Near miss explained.** After 963744 the transition's first jump test succeeded (`j = 0`), so
  the scan ran in class 0, which was empty. With `j = 1` it would have reached 930058, one class-1
  scan away from 852655.

### Heuristic picture (not proved; corrected 26 November 2026)

Each landing is one chance to fill small numbers, and landings arrive about 8 per decade. Define
a landing's depth as `D = log10(step / value)`. Chaffin's landings fall into two populations
(details in `PROOF_PLAN.md`):

- **The bulk has the same distribution at every scale from 10²⁰ to 10⁶¹².** Its median `D` is
  about 7.4, and its tail is exponential: the count drops by a factor of about 2.6 every 5
  decades. On its own, this would make landings below a fixed bound exponentially rare. Then only
  finitely many more small numbers would ever be filled, and the conjecture would be false.
- **Free falls.** Six landings after 10⁵⁰ fell 80 to 220 decades, where the bulk predicts about
  0.01 such events. That is roughly one every 90 decades. Each plunged 21–84% of the way down in
  log scale, and the 10⁴¹ fall to 2023155 went 85% of the way.

Free falls decide the question. Suppose they keep arriving at a steady rate, and the fraction
of the way down they plunge has any density near 100%. Then infinitely many of them reach the
bottom, because the expected count grows like the logarithm of the number of decades. Each
surviving hole would keep getting chances, which favours the conjecture being **true**, with
successive fills doubly-exponentially far apart. If free falls thin out, or never plunge
almost all the way, the conjecture is false. Seven events cannot tell these cases apart.

This replaces my earlier claim that the chance of a deep landing "decays geometrically per
decade, so the conjecture is probably false". That holds only for the bulk.

## 4. Where a formal proof would have to go

**Update:** the phased plan is now in `PROOF_PLAN.md`. Target 2 below turned out to be close to
a restatement of its own conclusion: `occurs_iff` already reduces 852655 to the single equation
`a k = k + 852656`. The plan therefore does not count it as progress.

The `window` theorem reduces the fate of 852655 to one statement about the future of the walk.
Concretely:

- **Disproof of the conjecture, via 852655.** Prove that for all `n` beyond some bound, no
  landing (jump into a zigzag) occurs at height in `[852656, 930056]` with the right residue. The
  cleanest stronger statement would be something like **"landing values eventually exceed every
  fixed bound"**, i.e. `∀ B, ∃ N, ∀ n ≥ N, a landing at step n has value > B`. Chaffin's data
  suggests `value ≥ n^0.9` for all but three landings after 10⁵⁰. Any proof needs an invariant or
  monotone quantity controlling how close `a(n) mod n` can get to 0 at a wrap. None is known.
- **Proof of the conjecture.** You would need the opposite: landings that dip below every bound
  infinitely often, with residues lining up. The data argues against it.
- **Concrete intermediate formal targets:**
  1. Formalize Chaffin's claim that `a(n) mod n` is non-increasing except at wraparounds, or
     characterize exactly when it increases. Define *landing* in Lean and prove that small numbers
     can only be filled at landings. This links the `window` theorem to A393814.
  2. State "landing values eventually exceed `B`" as a `Prop` and prove it implies
     `¬ SloaneConjecture`. That isolates the single open hypothesis.
  3. Verify the interval algorithm in Lean, so computational facts (e.g. "852655 ∉ a(0..10¹⁸)")
     become theorems.

## Sources

- OEIS [A005132](https://oeis.org/A005132), [A065052](https://oeis.org/A065052),
  [A393814](https://oeis.org/A393814), [A171884](https://oeis.org/A171884),
  [A064227](https://oeis.org/A064227)
- B. Chaffin, [Computing the Recamán Sequence](https://benchaffin.com/recaman/recaman.html),
  Feb 2026, with [holes below 2³²](https://benchaffin.com/recaman/rec-holes-2_32.txt) and
  [landings to 10⁶¹²](https://benchaffin.com/recaman/rec-landings-1e612.txt)
- [Three Cousins of Recamán's Sequence](https://arxiv.org/abs/2004.14000)
- ["A Handbook of Integer Sequences" Fifty Years Later](https://arxiv.org/abs/2301.03149)
- [Finding Structure in Sequences of Real Numbers via Graph Theory](https://arxiv.org/abs/2012.04625)
- [Seven Staggering Sequences](https://arxiv.org/abs/0912.2394)
- [Recamán's sequence (Wikipedia)](https://en.wikipedia.org/wiki/Recam%C3%A1n's_sequence)
