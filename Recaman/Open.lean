import Recaman.Counting

/-!
# Open statements, stated precisely

Nothing here is proved; these are the targets left open by Phases 1–4, as exact `Prop`s.
-/

namespace Recaman

/-- Open: the walk drops below the diagonal infinitely often (`a n < n`), i.e. it keeps making
landings in Chaffin's sense. Observed: about 28.5% of the first `10^9` steps end below it. -/
def BelowDiagonalInfinitelyOften : Prop := ∀ N, ∃ n, N ≤ n ∧ a n < n

/-- Open, and possibly false: `a n = O(n)`. Observed: `max_{m ≤ n} a m / m` is 4 by `10^3`,
7 by `10^5` and 8 by `10^9`, so it may grow without bound, slowly. -/
def LevelBounded : Prop := ∃ C, ∀ n, a n ≤ C * n

theorem lev_le_of_bounded {C : Nat} (h : ∀ n, a n ≤ C * n) (m : Nat) (hm : 1 ≤ m) : lev m ≤ C := by
  unfold lev
  exact (Nat.div_le_iff_le_mul_add_pred (by omega)).2 (by have := h m; rw [Nat.mul_comm] at this; omega)

/-- What `LevelBounded` would give: at most `(C + 1) k` wraps by step `2^k`, and backward steps
(each landing on a new number) make up half of all steps up to `O(C log n)`. -/
theorem density_of_levelBounded (h : LevelBounded) :
    ∃ C, ∀ k, 2 ^ k ≤ 2 * nback (2 ^ k) + C + (C + 1) * k := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, nback_pow_two (lev_le_of_bounded hC)⟩

end Recaman
