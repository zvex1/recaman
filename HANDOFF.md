# Handoff: Sloane's conjecture for Recamán's sequence

To the next agent. This is everything a previous session established, what it ruled out, and where
it got stuck. Read it fully before starting: several obvious lines of attack are already known
to fail, and the notes below say why.

## 1. The problem

`a(0) = 0`; `a(n) = a(n-1) - n` if that is positive and not already in the sequence, otherwise
`a(n-1) + n` (OEIS A005132). **Sloane's conjecture** (1991): every natural number occurs.

It is **open**. The literature review (`LITERATURE_AND_FINDINGS.md`) found no proof, disproof or
non-trivial partial result anywhere, and no prior formal work. The smallest missing number has
been **852655** since 10¹⁵ steps (Wilks, 2001), and Chaffin's computation shows it still missing
after **10⁶¹²** steps (February 2026). Every source expects either answer to need a new idea.

The goal is a Lean proof of `Recaman.SloaneConjecture` or of its negation. A disproof would most
naturally show that 852655 never appears.

## 2. The repository

```
Recaman.lean            definitions, recurrence, zigzag/transition/cascade/window lemmas
Recaman/Clock.lean      level/offset law, wraps (Phase 1)
Recaman/Intervals.lean  verified balanced interval tree (Phase 2)
Recaman/Fast.lean       verified phase-level evaluator: run_spec, check2_sound (Phase 2)
Recaman/Wilks.lean      verified computations: occur_below_1355, wilks, fate_852655 (Phase 3)
Recaman/Counting.lean   exact counting identities (Phase 4)
Recaman/Cascade.lean    self-driven restart lemma (Phase 5a)
Recaman/Open.lean       open statements as exact Props
Recaman/Audit.lean      #print axioms for everything
sim/                    C++ simulators and instrumentation, with saved outputs
data/                   Chaffin's holes below 2^32 and all landings to 10^612
PROOF_PLAN.md           the phased plan, with a status section per phase
LITERATURE_AND_FINDINGS.md   literature review and heuristics
```

### Build

- **Toolchain:** Lean 4.36.0 core only, with no Mathlib. `lean-toolchain` pins the version.
- **Build:** run `lake build`. A clean build takes about 7 minutes, almost all of it two proofs:
  - `wilks`: a 10¹⁵-step `native_decide` run, about 6 minutes;
  - `occur_below_1355`: a kernel check, about 1 minute.
- **Precompiled modules:** the lakefile sets `precompileModules = true`, so `native_decide` runs
  at native speed. Keep it on.
- **Command-line evaluator:** `lake build fastcheck` builds it. For example,
  `.lake/build/bin/fastcheck 1000000000000` prints `a(N)`, the smallest missing number and the
  interval count. It reaches 10¹² steps in about 10 s and 10¹⁵ in about 5 minutes.
- **Standards kept so far:**
  - no `sorry` anywhere;
  - every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`;
  - the one exception is that `wilks` and `fate_852655` also depend on the `native_decide`
    axiom `Recaman.check_wilks._native.native_decide.ax_1_1`.

  The audit prints all of this on every build. Please keep these standards, and state any new
  trust assumption explicitly.

## 3. What is proved (all machine-checked)

Core definitions (`Recaman.lean`):
- `a : Nat → Nat`.
- `Visited n x` means `x ∈ {a 0, …, a n}`.
- `Back n` means step `n+1` goes backward.
- `SloaneConjecture : ∀ m, ∃ n, a n = m`.

| Name | Statement (informal) |
|---|---|
| `occurs_iff`, `sloane_iff` | `m` occurs ⟺ `m ∈ {a 0..a m}` or `a k = k + m + 1` for some `k` (the walk stands exactly `m+1` above the diagonal). |
| `zigzag`, `zigzag_odd`, `zigzag_jump` | After landing on `x` at step `k`, the walk alternates `x, x+k+1, x−1, x+k+2, …` through the free run below `x`. Its jump tests are `x−k−1−3j`; the first free test is jumped onto. |
| `transition`, `cascade`, `cascade_class` | A drained run ending at `ℓ` restarts the walk at `2t+ℓ−6`. The next landing is `ℓ−8−5j` above the diagonal and scans residue class `(ℓ+j) mod 3`. |
| `entry`, `entry_exposed` | Late on, a hole with an occupied upper neighbour is entered only by two consecutive backward steps. |
| `window`, `window_suff` | If all of `(m, m′)` is visited, with `m ≡ m′ mod 3`, then `m` appears later iff a jump lands exactly `m+1+3j ≤ m′−2` above the diagonal and the following zigzag runs down to `m`. |
| `clock_fwd/back/fwd_wrap/back_wrap` | With `lev n = a n / n` and `off n = a n % n`: each step does `off ← off − lev` and `lev ← lev ± 1`. When `off < lev` it instead wraps: `off ← off − lev + n + 1`, and `lev` changes by `0` (forward) or `−2` (backward). |
| `wrap_between` | Some wrap occurs in every stretch `[n, 3n)`. |
| `below_diag_antitone` | Between two wraps, terms below the diagonal are non-increasing. |
| `fill_iff` | For `y+1 < n`: step `n+1` lands on a new `y` ⟺ `lev n = 1 ∧ off n = y+1`. |
| `run_spec`, `check2_sound` | The interval-tree evaluator computes `a N` and the exact visited set. |
| `occur_below_1355` | Kernel-checked: every `m < 1355` occurs within 10⁶ terms; 1355 does not. |
| `wilks` | Every `m < 852655` occurs within 10¹⁵ terms; 852655 does not. |
| `fate_852655` | If 852655 occurs at step `n`, then `n > 10¹⁵` and either 930058 occurred first, or a jump landed between 852656 and 930056 above the diagonal at step `n−1−2j`. No data hypotheses. |
| `back_count` | `2·#backward steps + lev n + #wraps = n`, exactly. |
| `off_add_slev` | `off n + Σ lev = Σ (m+1)` over the wraps, exactly. |
| `nwrap_pow_three` | At least `k` wraps by step `3^k`. |
| `density_of_levelBounded` | If `a n ≤ C n`, then wraps are `O(C log n)` and half of all steps go backward to new numbers. |
| `restart_test_self`, `restart_jump_index` | After draining a run of `r` rounds, the restart's tests inside the run it just wrote fail automatically, so any jump has `r < 3j + 4`. |

## 4. What the data shows

Each fact below says which tool or file backs it.

**Freezing.** There were 13 holes below 976368 at 10¹⁸, and all are still there at 10⁶¹². They
are in residue classes 1 and 2 only; class 0 below 976368 is empty.

**Landing depth** (Chaffin's 5,104 landings). Define `D = log10(step/value)`.
- **The bulk is scale-invariant.** It has the same distribution from 10²⁰ to 10⁶¹²: median 7.4,
  with an exponential tail that loses a factor of about 2.6 every 5 decades.
- **Free falls are a separate population.** Six landings after 10⁵⁰ fell 80–220 decades, about
  one per 90 decades, each plunging 21–84% of the way down in log scale.
- **The heuristic direction is undecided.** If free falls recur and can plunge arbitrarily
  close to 100%, infinitely many reach the bottom, and the conjecture is heuristically true with
  doubly-exponential spacing. Otherwise it is false.

**Passes.** Every pass between wraps dips below the diagonal, usually within its first 0.1% of
steps, because the last zigzag of a pass runs through the wrap (`sim/passes.c`). The maximum of
`a n / n` keeps rising slowly: 4 by 10³, 7 by 10⁵, 8 by 10⁹. Backward steps have density
exactly ½ up to 10⁹.

**Cascades are self-driven, increasingly with scale** (`sim/cascade_probe.cpp`,
`sim/cascade_report_*.txt`).
- **Who blocks the jump tests.** In restarts after 10¹⁵, 99.4% of failed jump tests hit numbers
  the cascade itself wrote, and only 4 of 680 restarts were blocked by older numbers. The
  self-driven share is 86% after 10⁶ and 97.5% after 10¹².
- **The local rule.** The restart's first test is always exactly 4 below the top of the run the
  cascade just wrote. When the next test is fresh, `j` depends only on the run length, and a
  single hole keeps the residue class.
- **How late scans die.** Mostly on an empty residue class below them.

**The fresh-frontier model** (`sim/shadow.cpp`, `sim/entries.cpp`). The model is the exact
walk, keeping only the visited numbers below a bound plus the cascade's own writes, with every
other number free.
- **Validation.** After 10¹⁵ the real cascade is a prefix of the model's in 3 of 5 cascades,
  with an exact 430-hole match for the 9·10¹⁷ cascade. Earlier, the model runs far deeper than
  reality. Older visits mostly *kill* cascades early rather than redirect them.
- **On Chaffin's 10⁶¹² hole set,** entering at every hole under 6 start times:
  - 3,035 of 3,102 entries end at the hole **2023215**, a barrier;
  - **43 entries reach 852655**, all holes below 15.3 million;
  - in the model, 852655 is filled exactly when the walk lands at level 1 with its first jump
    test in one of 43 explicit windows (`sim/windows_852655.txt`). That is 5.28 million values
    between 852655 and 16.3 million.

  So the hole structure alone does **not** protect 852655.

## 5. Dead ends, so you don't repeat them

1. **The conditional theorem "if landings stay above B forever, the conjecture fails"** is a
   near-tautology, because `occurs_iff` already reduces 852655 to `a k = k + 852656`. It is not
   progress.
2. **The structural disproof via the hole set** ("no cascade can reach 852655") is false in the
   fresh-frontier model: §4 lists 43 reaching entries.
3. **Counting arguments for `BelowDiagonalInfinitelyOften` (4b) don't work.** That statement is
   about where free runs end relative to the diagonal, not about densities.
4. **`LevelBounded` (`a n = O(n)`) may be false**, because the observed maximum level keeps
   rising. Don't build on it without evidence.
5. **No mod-3 invariant comes from the parity law.** The parity law
   (`a n odd ⟺ n ≡ 1,2 mod 4`) fixes no residue mod 3 of the cascade index `j`. It only gives a
   consistency condition that is satisfied automatically.
6. **"Probably false" was overstated** in early notes; see the free-fall analysis in §4.

## 6. Where a proof would have to come from

Both directions reduce to controlling **how close landings get to the diagonal, forever**. That
closeness is decided by "fossils": numbers visited long before that happen to sit near the
current frontier.

- **Disproof:** after step 10¹⁵ (or any computed point), the walk never lands at level 1 with a
  first jump test in the windows of §4, or never inside `[852656, 930056]` (`fate_852655`). This
  is very likely true: nothing has landed below 10²⁷ since about step 10¹⁶⁷.
- **Proof:** free falls reach every hole, in every residue pattern, infinitely often.

The previous session found no tool for either. The candidates that could change that:

1. **A renormalization theorem.** An exact description of the visited set near the diagonal at
   time `t` in terms of the walk at times about `t/q`, at level `q`. The scale-invariant bulk of
   the landing-depth distribution is a strong hint that such a self-similar structure exists.
   The open question is whether it is exact enough to induct on.
2. **An invariant forbidding residue patterns**, in the spirit of class 0 being empty below
   976368. It would show that the classes a deep cascade can arrive in are constrained forever.
3. **A proof of the fresh-frontier hypothesis** past some time, plus a bound on how close to the
   diagonal a level-1 landing can occur. This converts the model's 43 windows into a theorem.

### Precise intermediate targets (Lean)

- `Recaman.BelowDiagonalInfinitelyOften : ∀ N, ∃ n, N ≤ n ∧ a n < n` (open).
- `Recaman.LevelBounded : ∃ C, ∀ n, a n ≤ C * n` (open, possibly false).
- **The fresh-frontier reduction as a conditional theorem.** Under an explicit hypothesis that
  no number visited before a cascade lies in the tested region, show that filling 852655
  requires a landing in the listed windows.
- **An exact cascade transition function** on hole sets. Extend `restart_jump_index` to "the
  scan class equals `(ℓ + j) mod 3` with `j` a function of the run length", under freshness.

## 7. Practical notes

- **Simulator:** `sim/recaman_fast.cpp` uses the same algorithm as Chaffin and as the verified
  evaluator. It needs `u64` values, so it is limited to about 10¹⁸ steps, which take about 8
  minutes. It matches a direct simulation at 10 checkpoints up to 10⁹, and the verified
  evaluator at 10⁶, 10⁹, 10¹² and 10¹⁵.
- **Instrumentation:**
  - `sim/cascade_probe.cpp --cascade B` logs every zigzag of every cascade below `B`;
  - `sim/shadow.cpp N B KMIN` runs the validation against the fresh-frontier model;
  - `sim/entries.cpp data/rec-holes-2_32.txt [entry-list]` runs the entry experiment.
- **Chaffin's data:**
  - `data/rec-holes-2_32.txt` lists the holes below 2³² after 10⁶¹² steps, one hole or range
    `a - b` per line;
  - `data/rec-landings-1e612.txt` lists all landings, as lines `landing: r[step] = value`.

  Both come from benchfin.com/recaman.
- **Kernel limits:** kernel-only checks (`decide +kernel`) cost about 50 s at 10⁶ steps and grow
  about 4× per decade, so use `native_decide` beyond about 10⁷.

## 8. Honest assessment

The formal infrastructure is solid and ready to use. The mathematical core is a statement about
a deterministic process that behaves pseudo-randomly. That puts it in the same class as the
Collatz conjecture, where no existing technique gives "never" or "infinitely often" results.

A resolution needs a genuinely new idea, most plausibly an exact self-similarity of the frontier.
Please test any idea against the data in `sim/` and `data/` before investing in a proof, and
report negative results as plainly as positive ones.
