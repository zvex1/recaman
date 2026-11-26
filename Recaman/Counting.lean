import Recaman.Clock
set_option linter.deprecated false

/-!
# Counting backward steps and wraps (Phase 4)

Two exact identities, from the four cases of the clock law:

* `back_count`: `2 · #backward steps + lev n + #wraps = n`. So backward steps have density
  exactly `1/2` as soon as the level and the number of wraps are `o(n)`.
* `off_add_slev`: `off n + Σ_{m<n} lev m = Σ_{wraps m<n} (m + 1)`. Each wrap at time `m` pays
  for about `m` units of level.

Consequences: there are at least `k` wraps by step `3^k` (unconditional), and *if* the level is
bounded by `C`, there are at most `(C+1)k` wraps by step `2^k`, so backward steps (hence distinct
values) have density `1/2`. Whether the level is bounded is open: computationally the maximum
of `a n / n` creeps up (4 by `10^3`, 7 by `10^5`, 8 by `10^9`).
-/

namespace Recaman

/-- Backward steps among steps `m → m+1` with `1 ≤ m < n`. -/
def nback : Nat → Nat
  | 0 => 0
  | n + 1 => nback n + if 1 ≤ n ∧ Back n then 1 else 0

/-- Wraps among steps `m → m+1` with `1 ≤ m < n`. -/
def nwrap : Nat → Nat
  | 0 => 0
  | n + 1 => nwrap n + if 1 ≤ n ∧ Wrap n then 1 else 0

/-- `Σ_{1 ≤ m < n} lev m`. -/
def slev : Nat → Nat
  | 0 => 0
  | n + 1 => slev n + if 1 ≤ n then lev n else 0

/-- `Σ (m + 1)` over the wraps `1 ≤ m < n`. -/
def swrap : Nat → Nat
  | 0 => 0
  | n + 1 => swrap n + if 1 ≤ n ∧ Wrap n then n + 1 else 0

theorem lev_one : lev 1 = 1 := by decide
theorem off_one : off 1 = 0 := by decide

/-- **Exact count of backward steps.** -/
theorem back_count {n : Nat} (hn : 1 ≤ n) : 2 * nback n + lev n + nwrap n = n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [nback, nwrap, lev_one]
    have ih := ih hpos
    have e1 : nback (n + 1) = nback n + if 1 ≤ n ∧ Back n then 1 else 0 := rfl
    have e2 : nwrap (n + 1) = nwrap n + if 1 ≤ n ∧ Wrap n then 1 else 0 := rfl
    rw [e1, e2]
    by_cases hw : Wrap n
    · by_cases hb : Back n
      · have := clock_back_wrap hpos hb hw
        rw [if_pos ⟨hpos, hb⟩, if_pos ⟨hpos, hw⟩]; omega
      · have := clock_fwd_wrap hpos hb hw
        rw [if_neg (fun h => hb h.2), if_pos ⟨hpos, hw⟩]; omega
    · have hw' : lev n ≤ off n := by unfold Wrap at hw; omega
      by_cases hb : Back n
      · have := clock_back hpos hb hw'
        rw [if_pos ⟨hpos, hb⟩, if_neg (fun h => hw h.2)]; omega
      · have := clock_fwd hpos hb hw'
        rw [if_neg (fun h => hb h.2), if_neg (fun h => hw h.2)]; omega

/-- **Exact offset bookkeeping.** -/
theorem off_add_slev {n : Nat} (hn : 1 ≤ n) : off n + slev n = swrap n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [slev, swrap, off_one]
    have ih := ih hpos
    have e1 : slev (n + 1) = slev n + if 1 ≤ n then lev n else 0 := rfl
    have e2 : swrap (n + 1) = swrap n + if 1 ≤ n ∧ Wrap n then n + 1 else 0 := rfl
    rw [e1, e2, if_pos (show 1 ≤ n from hpos)]
    by_cases hw : Wrap n
    · have hq := lev_le n
      have : off (n + 1) = n + 1 + off n - lev n := by
        by_cases hb : Back n
        · exact (clock_back_wrap hpos hb hw).2
        · exact (clock_fwd_wrap hpos hb hw).2
      rw [if_pos ⟨hpos, hw⟩]; omega
    · have := off_succ hpos hw
      rw [if_neg (fun h => hw h.2)]; omega

theorem nwrap_mono {n d : Nat} : nwrap n ≤ nwrap (n + d) := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have e : nwrap (n + (d + 1)) = nwrap (n + d) + (if 1 ≤ n + d ∧ Wrap (n + d) then 1 else 0) := rfl
    rw [e]; omega

theorem nwrap_lt_of_wrap {n m n' : Nat} (h1 : n ≤ m) (h2 : m < n') (hm : 1 ≤ m) (hw : Wrap m) :
    nwrap n + 1 ≤ nwrap n' := by
  have a1 : nwrap n ≤ nwrap m := by
    have := nwrap_mono (n := n) (d := m - n); rwa [show n + (m - n) = m by omega] at this
  have a2 : nwrap (m + 1) ≤ nwrap n' := by
    have := nwrap_mono (n := m + 1) (d := n' - (m + 1)); rwa [show m + 1 + (n' - (m + 1)) = n' by omega] at this
  have a3 : nwrap (m + 1) = nwrap m + 1 := by simp [nwrap, hw, hm]
  omega

/-- **At least `k` wraps by step `3^k`.** -/
theorem nwrap_pow_three (k : Nat) : k ≤ nwrap (3 ^ k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hpos : 1 ≤ 3 ^ k := Nat.pow_pos (by decide : 0 < 3)
    obtain ⟨m, h1, h2, hw⟩ := wrap_between hpos
    have := nwrap_lt_of_wrap h1 (show m < 3 ^ (k + 1) by rw [Nat.pow_succ]; omega) (by omega) hw
    omega

/-- Over a block of `d` steps the wrap sum grows by at least `(n+1)` per wrap. -/
theorem swrap_block (n d : Nat) : swrap n + (nwrap (n + d) - nwrap n) * (n + 1) ≤ swrap (n + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hm := nwrap_mono (n := n) (d := d)
    have e1 : swrap (n + (d + 1)) = swrap (n + d) + (if 1 ≤ n + d ∧ Wrap (n + d) then n + d + 1 else 0) := rfl
    have e2 : nwrap (n + (d + 1)) = nwrap (n + d) + (if 1 ≤ n + d ∧ Wrap (n + d) then 1 else 0) := rfl
    rw [e1, e2]
    split
    · rename_i h
      rw [show nwrap (n + d) + 1 - nwrap n = (nwrap (n + d) - nwrap n) + 1 by omega, Nat.add_mul]
      omega
    · omega

theorem slev_block {C : Nat} (hC : ∀ m, 1 ≤ m → lev m ≤ C) (n d : Nat) :
    slev (n + d) ≤ slev n + C * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have e1 : slev (n + (d + 1)) = slev (n + d) + (if 1 ≤ n + d then lev (n + d) else 0) := rfl
    rw [e1, Nat.mul_succ]
    split
    · have := hC (n + d) (by omega); omega
    · omega

/-- **If the level is bounded by `C`, a doubling of time brings at most `C + 1` wraps.** -/
theorem nwrap_double {C : Nat} (hC : ∀ m, 1 ≤ m → lev m ≤ C) {n : Nat} (hn : 1 ≤ n) :
    nwrap (2 * n) ≤ nwrap n + C + 1 := by
  have e1 := off_add_slev hn
  have e2 := off_add_slev (n := 2 * n) (by omega)
  have b1 := swrap_block n n
  have b2 := slev_block hC n n
  rw [show n + n = 2 * n by omega] at b1 b2
  have o2 := off_lt (show 0 < 2 * n by omega)
  have hm := nwrap_mono (n := n) (d := n)
  rw [show n + n = 2 * n by omega] at hm
  -- `(Δw) (n + 1) ≤ off (2n) + C n < (C + 2) (n + 1)`
  have key : (nwrap (2 * n) - nwrap n) * (n + 1) < (C + 2) * (n + 1) := by
    have : (nwrap (2 * n) - nwrap n) * (n + 1) ≤ 2 * n + C * n := by omega
    have : 2 * n + C * n < (C + 2) * (n + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one]; omega
    omega
  have := Nat.lt_of_mul_lt_mul_right key
  omega

/-- **Bounded level ⇒ backward steps have density 1/2**: with `lev ≤ C` throughout, at least
`(2^k - C - (C+1) k) / 2` of the first `2^k` steps go backward, each to a new number. -/
theorem nback_pow_two {C : Nat} (hC : ∀ m, 1 ≤ m → lev m ≤ C) (k : Nat) :
    2 ^ k ≤ 2 * nback (2 ^ k) + C + (C + 1) * k := by
  have hw : nwrap (2 ^ k) ≤ (C + 1) * k := by
    induction k with
    | zero => simp [nwrap]
    | succ k ih =>
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have := nwrap_double hC hpos
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mul_succ]
      omega
  have := back_count (n := 2 ^ k) Nat.one_le_two_pow
  have := hC (2 ^ k) Nat.one_le_two_pow
  omega

end Recaman
