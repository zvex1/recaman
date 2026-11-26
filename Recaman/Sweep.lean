import Recaman.Wilks
import Recaman.Clock

/-!
# One chance per sweep

A *sweep* is a stretch of steps with no wrap: the offset `off n = a n % n` only goes down
(`off_antitone`). This module shows that the fate of `852655` is decided by the clock alone:

* `one_chance`: in a sweep, the walk can be at level 1 with offset `y + 1` at most once, so each
  sweep gives each small number at most one chance to be filled.
* `lev_ne_zero_in_window`, `fwd_in_window`: after `10^15`, while the offset is between
  `852656` and `930057`, the walk is never below the diagonal, and a step at level 1 always goes
  forward to level 2. So inside the window the walk lives on levels `≥ 1`, and its level-1 visits
  are isolated.
* `occurs_852655_iff`: `852655` ever occurs if and only if, at some step after `10^15`, the walk
  is at level 1 with offset exactly `852656` (with `852655` still unvisited).
-/

namespace Recaman

/-- **One chance per sweep.** If the walk is at level 1 with offset `y + 1` at step `i`, then at
every later step of the same sweep the offset is at most `y`. -/
theorem one_chance {i j y : Nat} (hi : 1 ≤ i) (hij : i < j)
    (nw : ∀ m, i ≤ m → m < j → ¬ Wrap m) (hl : lev i = 1) (ho : off i = y + 1) :
    off j ≤ y := by
  have e := off_succ hi (nw i (Nat.le_refl i) hij)
  have := off_antitone (i := i + 1) (j := j) (by omega) (by omega)
    (fun m h1 h2 => nw m (by omega) h2)
  omega

/-- Every number from `852656` to `930057` has occurred by step `10^15 - 77407`. -/
theorem window_visited {v : Nat} (h1 : 852656 ≤ v) (h2 : v ≤ 930057) :
    Visited 999999999922593 v := by
  obtain ⟨hc, _⟩ := check2_sound (by decide) (by decide) check_wilks
  exact hc (852656, 930057) (by simp) v (by simpa using h1) (by simpa using h2)

/-- **No landing inside the window.** After `10^15`, while the offset is between `852656` and
`930057`, the walk is not below the diagonal. -/
theorem lev_ne_zero_in_window {n : Nat} (hn : 1000000000000000 < n)
    (h1 : 852656 ≤ off n) (h2 : off n ≤ 930057) : lev n ≠ 0 := by
  intro h0
  have d := decomp n
  rw [h0, Nat.zero_mul, Nat.zero_add] at d
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases back_or_fwd k with ⟨hb, _⟩ | ⟨_, e⟩
  · apply (back_new hb).2
    rw [d]
    exact (window_visited h1 h2).mono (by omega)
  · have := off_lt (show 0 < k + 1 by omega)
    omega

/-- **Level 1 is a reflecting wall inside the window.** After `10^15`, at level 1 with offset
between `852658` and `930058`, the walk cannot step back (the number below is already taken), so
it steps forward to level 2. -/
theorem fwd_in_window {n : Nat} (hn : 1000000000000000 < n) (hl : lev n = 1)
    (h1 : 852658 ≤ off n) (h2 : off n ≤ 930058) : ¬ Back n ∧ lev (n + 1) = 2 := by
  have d := decomp n
  rw [hl, Nat.one_mul] at d
  have hnb : ¬ Back n := by
    intro hb
    apply hb.2
    rw [show a n - (n + 1) = off n - 1 by omega]
    exact (window_visited (by omega) (by omega)).mono (by omega)
  refine ⟨hnb, ?_⟩
  have := clock_fwd (by omega) hnb (by omega)
  omega

/-- **The fate of 852655 is a statement about the clock.** `852655` occurs if and only if, at
some step `n ≥ 10^15`, the walk is at level 1 with offset exactly `852656` while `852655` is
still unvisited. By `one_chance`, each sweep offers at most one such step. -/
theorem occurs_852655_iff :
    (∃ n, a n = 852655) ↔
      ∃ n, 1000000000000000 ≤ n ∧ lev n = 1 ∧ off n = 852656 ∧ ¬ Visited n 852655 := by
  constructor
  · rintro ⟨n, hn⟩
    induction n using Nat.strongRecOn with
    | ind n ih =>
      have hbig : 1000000000000000 < n := by
        apply Classical.byContradiction
        intro h
        exact wilks.2 n (by omega) hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      by_cases hv : Visited k 852655
      · obtain ⟨i, hi, e⟩ := hv
        exact ih i (by omega) e
      · have := (fill_iff (n := k) (y := 852655) (by omega)).1 ⟨hn, hv⟩
        exact ⟨k, by omega, this.1, this.2.1, hv⟩
  · rintro ⟨n, hn, hl, ho, hv⟩
    exact ⟨n + 1, ((fill_iff (n := n) (y := 852655) (by omega)).2 ⟨hl, ho, by decide, hv⟩).1⟩

end Recaman
