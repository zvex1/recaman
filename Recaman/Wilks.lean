import Recaman.Fast

/-!
# Verified computations

Both theorems below run the verified evaluator of `Recaman.Fast`.

* `occur_below_1355` is checked by the kernel itself (`decide +kernel`, about a minute).
* `wilks` re-derives the 2001 Bell Labs result (Wilks): every `m < 852655` occurs within the
  first `10^15` terms and `852655` does not. Running `10^15` steps is beyond the kernel, so this
  one uses `native_decide`: the evaluator is compiled and run, and Lean trusts that its compiler
  produced the right answer. In the axiom audit this appears as the extra axiom
  `Recaman.check_wilks._native.native_decide.ax_1_1`, and only
  `wilks`, `fate_852655` and the `check_wilks` certificate depend on it.
-/

namespace Recaman

theorem check_small : check2 1000000 1000000 [(0, 1354)] [1355] = true := by decide +kernel

/-- **Kernel-checked.** Every `m < 1355` occurs within the first `10^6` terms; `1355` does not. -/
theorem occur_below_1355 :
    (∀ m, m < 1355 → ∃ n, n ≤ 1000000 ∧ a n = m) ∧ ∀ n, n ≤ 1000000 → a n ≠ 1355 := by
  obtain ⟨hc, hm⟩ := check2_sound (by decide) (Nat.le_refl _) check_small
  refine ⟨fun m h => ?_, fun n hn e => hm 1355 (by simp) ⟨n, hn, e⟩⟩
  obtain ⟨n, hn, e⟩ := hc (0, 1354) (by simp) m (Nat.zero_le _) (by simp; omega)
  exact ⟨n, hn, e⟩

/-- The certificate for `wilks`: run to step `10^15 - 77407`, check that everything below
`852655` and everything strictly between `852655` and `930058` has occurred; run on to step
`10^15` and check that `852655` and `930058` still have not. -/
theorem check_wilks :
    check2 999999999922593 1000000000000000 [(0, 852654), (852656, 930057)] [852655, 930058] =
      true := by native_decide

/-- **Wilks's computation, formally checked** (with `native_decide`). Every `m < 852655` occurs
among the first `10^15` terms, and `852655` does not. -/
theorem wilks : (∀ m, m < 852655 → ∃ n, n ≤ 1000000000000000 ∧ a n = m) ∧
    ∀ n, n ≤ 1000000000000000 → a n ≠ 852655 := by
  obtain ⟨hc, hm⟩ := check2_sound (by decide) (by decide) check_wilks
  refine ⟨fun m h => ?_, fun n hn e => hm 852655 (by simp) ⟨n, hn, e⟩⟩
  obtain ⟨n, hn, e⟩ := hc (0, 852654) (by simp) m (Nat.zero_le _) (by simp; omega)
  exact ⟨n, by omega, e⟩

/-- **The fate of 852655, unconditionally.** If `852655` ever occurs, at step `n`, then
`n > 10^15`, and either `930058` occurred first, or the walk got there by a jump landing between
`852656` and `930056` above the diagonal followed by a zigzag down to it. This removes the data
hypotheses of `window_852655`. -/
theorem fate_852655 {n : Nat} (ha : a n = 852655) :
    1000000000000000 < n ∧ (Visited (n - 1) 930058 ∨ ∃ j, 852656 + 3 * j ≤ 930056 ∧
      a (n - 1 - 2 * j) = (n - 1 - 2 * j) + 852656 + 3 * j ∧
      Back (n - 2 - 2 * j) ∧ Back (n - 3 - 2 * j)) := by
  obtain ⟨hc, hm⟩ := check2_sound (by decide) (by decide) check_wilks
  have hn : 1000000000000000 < n := by
    apply Classical.byContradiction
    intro h
    exact hm 852655 (by simp) ⟨n, by omega, ha⟩
  refine ⟨hn, ?_⟩
  by_cases hv : Visited (n - 1) 930058
  · exact Or.inl hv
  · exact Or.inr (window_852655 (N := 999999999922593) (by decide)
      (fun v h1 h2 => hc (852656, 930057) (by simp) v (by simp; omega) (by simp; omega))
      hv (by omega) ha)

end Recaman
