# Plan of attack: a formal proof or disproof of Sloane's conjecture

Written 26 November 2026. Companion to `LITERATURE_AND_FINDINGS.md`.

## Status (26 November 2026, after Phases 1–4)

- **Phase 1, done.** `Recaman/Clock.lean`: the four cases of the clock law; a wrap in every
  stretch `[n, 3n)`; Chaffin's monotonicity (`below_diag_antitone`); `fill_iff`.
- **Phase 2, done.** `Recaman/Intervals.lean` and `Recaman/Fast.lean`: a verified interval tree
  and a phase-level evaluator (one zigzag or jump per step), proved to compute `a N` and the
  exact visited set (`run_spec`).
- **Phase 3, done.** `Recaman/Wilks.lean`: `occur_below_1355` (kernel only, `10^6` steps; the
  kernel costs grow about 4× per decade, so this is near its practical limit), `wilks`
  (`10^15` steps via `native_decide`, about 5 minutes) and `fate_852655`, which is
  `window_852655` without data hypotheses.
- **Phase 4, partly done.**
  - Proved: 4a (wraps), the exact identities `back_count` and `off_add_slev`, at least `k`
    wraps by step `3^k`, and 4d *conditional on* bounded level (`density_of_levelBounded`).
  - Not proved: 4b (`BelowDiagonalInfinitelyOften`) and 4c (`LevelBounded`), both stated in
    `Recaman/Open.lean`. 4c may be false: the maximum of `a n / n` reaches 8 by `10^9` and is
    still creeping up. `back_count` shows exactly what 4d needs: backward steps have density ½
    iff `lev n + #wraps = o(n)`.

## The situation

Every part of a formal proof is within reach except one: the exact rules of the walk, the
reductions and the computations can all be formalized. The exception is a statement about what
the walk does *forever*. Nobody has a method for that, and that is where 35 years of work have
stalled.

So this plan has two jobs. First, it banks theorems that are certainly provable and, as far as
the literature review found, new: nothing non-trivial about the walk's long-run behaviour has
been proved. Second, it attacks the "forever" statement through one specific mechanism, with a
rule for when to stop.

**A correction.** I earlier proposed the conditional theorem "if landings stay above `B` forever,
the conjecture fails". It is close to a restatement of its own conclusion. `occurs_iff` already
reduces "852655 appears" to "some step has `a k = k + 852656`". This plan does not count such
theorems as progress.

## Two facts established on 26 November

### The clock law (exact)

Write `q(n) = a(n) div n` (the *level*) and `r(n) = a(n) mod n` (the *offset*), for `n ≥ 1`.
At every step:

- if `r ≥ q`, then `r ← r − q`, and `q ← q + 1` (forward step) or `q ← q − 1` (backward step);
- if `r < q`, the offset **wraps**: `r ← r − q + n + 1`, and `q` stays the same (forward) or
  `q ← q − 2` (backward).

A direct check found no exceptions for `n ≤ 2·10⁶`, and the algebra takes three lines. This is the
exact form of Chaffin's observation that `a(n) mod n` only decreases until it wraps. Two
consequences follow at once:

- **Wraps never stop.** Between wraps the offset falls by the level at every step. A step at
  level 0 is always followed by a step at level 1, so the offset falls at least 1 every two
  steps. Since `r(n) < n`, some wrap occurs in every stretch from `n` to `3n`. Up to 2·10⁶ the
  largest ratio between consecutive wraps is exactly 2.
- **Holes are filled from level 1.** For `y + 1 < n`, step `n + 1` lands on a new number `y`
  exactly when `q(n) = 1` and `r(n) = y + 1`. This is `occurs_iff` in clock language.

### Which way the evidence points: undecided

Define a landing's **depth** as `D = log10(step / value)`. These are Chaffin's 5,104 landings up
to 10⁶¹²:

| step range | landings | median D | 90th percentile D |
|---|---|---|---|
| 10²⁰–10⁵⁰ | 253 | 7.10 | 13.7 |
| 10⁵⁰–10¹⁰⁰ | 424 | 7.35 | 15.0 |
| 10¹⁰⁰–10²⁰⁰ | 845 | 7.39 | 14.8 |
| 10²⁰⁰–10³⁰⁰ | 846 | 7.35 | 14.6 |
| 10³⁰⁰–10⁴⁰⁰ | 844 | 7.35 | 14.2 |
| 10⁴⁰⁰–10⁵⁰⁰ | 842 | 7.48 | 14.5 |
| 10⁵⁰⁰–10⁶¹² | 951 | 7.42 | 14.3 |

- **The bulk is scale-invariant.** It has the same distribution at every scale, with an
  exponential tail: 22% of landings fall more than 10 decades, 3.1% more than 20, 0.5% more
  than 30. On its own, this predicts that only finitely many more small numbers will ever be
  filled, so the conjecture would be false.
- **Free falls are a second population.** Six landings after 10⁵⁰ fell 80–220 decades; the bulk
  predicts about 0.01 such events.

  | step | value |
  |---|---|
  | 10¹⁶⁷ | 10²⁷ |
  | 10²⁴¹·⁸ | 10¹⁶⁰·³ |
  | 10²⁴⁸·⁹ | 10¹⁰¹·⁶ |
  | 10³¹¹·⁴ | 10⁹⁰·⁹ |
  | 10⁵⁴⁰·⁸ | 10⁴²⁶·² |
  | 10⁵⁸¹·² | 10⁴²⁰·⁰ |

  That is about one free fall per 90 decades, each plunging 21–84% of the way down in log scale.
  The fall at 10⁴¹ that reached 2023155 went 85% of the way.

Suppose free falls keep arriving at a steady rate, and the fraction of the way down they plunge
has any density near 100%. Then the expected number that reach the bottom grows like the
logarithm of the number of decades, so infinitely many do, and the conjecture is favoured to be
**true**. Seven events cannot decide this. **Either way, the answer turns on free falls.**

## Phases

### Phase 1: the clock in Lean (low risk; start here)

Core Lean, using `omega` and `grind`:

```lean
def lev (n : Nat) : Nat := a n / n
def off (n : Nat) : Nat := a n % n
-- clock_step : 1 ≤ n → lev n ≤ off n → off (n+1) = off n - lev n ∧ (level ±1 by direction)
-- clock_wrap : 1 ≤ n → off n < lev n → off (n+1) = n + 1 + off n - lev n ∧ (level 0 or -2)
-- wrap_between : 1 ≤ n → ∃ m, n ≤ m ∧ m < 3 * n ∧ off m < lev m
-- fill_iff : y + 1 < n → (a (n+1) = y ∧ ¬ Visited n y ↔ lev n = 1 ∧ off n = y + 1 ∧ ¬ Visited n y ∧ 0 < y)
-- Landing : the smallest term between consecutive wraps (Chaffin's landings, OEIS A393814)
```

Then restate `ladder_*`, `cascade` and `window` in clock coordinates wherever that makes them
simpler.

### Phase 2: phase-level semantics (medium)

Define a state `(n, cur, vis)`, with the visited set stored as intervals. Define `phase`, which
advances one whole zigzag, jump or transition, exactly as `sim/recaman_fast.cpp` does. Prove that
`phase` agrees with `state`, using the existing `zigzag`, `zigzag_jump` and `transition` lemmas.
Any long-run argument needs this vocabulary, and Phase 3 runs on it.

### Phase 3: verified computation (medium; needs one decision)

Implement the interval algorithm in Lean, proved correct by Phase 2.

- **Kernel only** (`decide +kernel`): this goes as far as the kernel can manage, which I would
  guess is 10⁷–10⁸ steps, still to be measured. It extends `small_occur` beyond `m < 19`.
- **Compiled evaluation** (`native_decide`, which also trusts Lean's compiler through
  `Lean.ofReduceBool`): this proves Wilks's 10¹⁵ result, that every `m < 852655` appears and
  852655 does not. That removes the data hypotheses of `window_852655`, so the fate of 852655
  becomes a statement purely about steps after 10¹⁵.

### Phase 4: first theorems about the infinite future (real chance; would be new)

- **4a. Wraps occur infinitely often**, at least once from `n` to `3n`. This follows from
  Phase 1 and is certain.
- **4b. `a n < n` for infinitely many `n`**: the walk keeps dropping below the diagonal. This
  looks plausible by counting the numbers the walk tests from level 1 against the numbers it
  never visits. Its difficulty is unknown.
- **4c. The level is bounded: `a n ≤ C·n`.** The maximum level up to 2·10⁶ is 7. So far I can
  only show that after reaching a new record level, the walk can go one level higher for at most
  one step. That is not yet a bound.
- **4d. A positive fraction of steps go backward**, so a positive fraction of the numbers up to
  `n` appear.

These need real counting arguments. This is where Mathlib (finite-set cardinalities and sums)
starts to pay for itself.

### Phase 5: the core, explaining free falls (research; long shot)

The goal is an exact rule, provable in Lean, for how deep a pass of the clock through 0 can go.
There are three hypotheses. Each one is tested on the simulator and on Chaffin's data before any
proof work:

- **5a. Cascades drive themselves.**
  - After a cascade eats a run of `r` holes, the transition's jump tests start just above the
    diagonal, near `t + ℓ`. That is where the cascade's own upper branch has just written `r`
    consecutive numbers. So roughly the first `r/3` tests fail for a reason inside the cascade.
  - If the tests beyond that run hit fresh numbers, then `j`, and with it the next scan class
    `(ℓ + j) mod 3`, depends on the hole set alone. The death after 963744, where `j = 0`, fits
    this.
  - If the hypothesis holds, cascades are a deterministic machine on the hole set. "Which holes
    can a cascade reach from above" then becomes a finite computation below any bound.
- **5b. Fossils.** When a test is blocked by a number visited long ago, record when it was
  visited. My prediction is that blocks near the diagonal at step `t` come from the walk at about
  step `t/q`, while it was at level `q`. If so, free falls happen when earlier passes left no
  fossils at the right ratios. That would give a concrete multi-scale recursion to formalize.
- **5c. How falls end.** Classify every cascade death after 10¹⁵ by its cause:
  1. an empty residue class, as with 963744;
  2. a run of holes long enough to push the next landing height `ℓ − 8 − 5j` below 0, which
     needs a run longer than about `0.6·ℓ`;
  3. a short free run;
  4. something else.

  If only the first two causes occur, the depth a free fall reaches depends only on how the holes
  are spread across residue classes at each scale.

**What a finished proof would look like.**
- **Disproof:** a property of (position, visited set) that holds at step 10¹⁵ (by Phase 3), is
  preserved by every phase (Phases 2 and 5), and excludes 852655.
- **Proof:** a recurrence theorem showing that free falls reach the bottom infinitely often, in
  every residue pattern.

**Stop rule.** Suppose 5a–5c show that how deep a fall goes depends on fossils at positions with
no exact description. Then the core needs control of a pseudo-random process forever, the same
territory as the Collatz problem, where no existing technique applies. In that case I say so
plainly, and we bank Phases 1–4.

## How the work runs

- **Statements come first.** Each target goes into `Plan.lean` as an exact Lean statement;
  `sorry` is allowed only there. `Recaman.lean` stays free of `sorry` and keeps its axiom audit.
- **Data before proofs.** Every Phase 5 hypothesis is checked against the data before any proof
  is attempted.
- **Parallel attempts on request.** Once statements are fixed, independent proof attempts can run
  in parallel, but only if asked.

## Decisions needed

1. **`native_decide` for Phase 3's large computation?** Recommendation: yes, kept in a separate
   file so the audit shows exactly which theorems use it.
2. **Mathlib from Phase 4?** Recommendation: yes once Phase 4 starts; stay core-only until then.
3. **Order of work.** Phase 1 first. Run the 5a and 5c tests early, because their answer decides
   whether Phase 5 is worth pursuing. Then Phases 2–4.
