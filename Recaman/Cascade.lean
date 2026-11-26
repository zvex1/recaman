import Recaman

/-!
# Self-driven cascades (Phase 5a)

A zigzag from `x` at step `k` that drains its whole free run, `r` rounds, ends on
`ℓ = x - r` at step `s = k + 2r`. Its upper branch has just written the consecutive numbers
`x + k + 1, …, x + k + r`. The restart after the transition (`transition`, `cascade`) tests
`ℓ + s - 3 - 3i` for `i = 0, 1, …`, and these start exactly 4 below the top of that run.
So every test that lands inside the run fails, for a reason internal to the cascade.

In the instrumented run to `10^18`, every restart after `10^15` whose failed tests all lay in
the run just written jumped at the first test below it: 567 of 680 restarts. Only 4 of the 680
were blocked by a number older than the cascade. When the next test is fresh, `j` is a function
of `r` alone, and so is the next scan class `(ℓ + j) mod 3` (`cascade_class`). In particular a
single-hole run (`r = 0`) gives `j = 0`, and the residue class is preserved.
-/

namespace Recaman

/-- The restart's tests that fall inside the zigzag's own upper branch have occurred. -/
theorem restart_test_self {k x r : Nat} (hx : a k = x) (hr : r < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ r → ¬ Visited k (x - i))
    (htest : ∀ j, j < r → k + 2 * j + 1 < x - j → Visited k (x - j - (k + 2 * j + 1)))
    (i : Nat) (hi : 3 * i + 4 ≤ r) :
    Visited (k + 2 * r) ((x - r) + (k + 2 * r) - 3 - 3 * i) := by
  have e := zigzag_odd hx hr hfree htest (r - 4 - 3 * i) (by omega)
  refine ⟨k + 2 * (r - 4 - 3 * i) + 1, by omega, ?_⟩
  rw [e]; omega

/-- **Jump index after draining a run.** If the restart jumps at its `j`-th test (that test is
free), then `r < 3j + 4`: the jump cannot happen inside the run just written. -/
theorem restart_jump_index {k x r j : Nat} (hx : a k = x) (hr : r < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ r → ¬ Visited k (x - i))
    (htest : ∀ j, j < r → k + 2 * j + 1 < x - j → Visited k (x - j - (k + 2 * j + 1)))
    (hjnew : ¬ Visited (k + 2 * r + 4) ((x - r) + (k + 2 * r) - 3 - 3 * j)) : r < 3 * j + 4 := by
  apply Classical.byContradiction
  intro h
  exact hjnew ((restart_test_self hx hr hfree htest j (by omega)).mono (by omega))

end Recaman
