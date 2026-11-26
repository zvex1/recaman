import Recaman

/-!
# The clock: level and offset

Write `a n = lev n * n + off n` with `off n < n`. Every step lowers the offset by the level,
`off (n+1) = off n - lev n`, and moves the level by `±1` — unless `off n < lev n`, when the
offset **wraps** up by `n + 1 - lev n` and the level moves by `0` or `-2`. This is the exact
form of Chaffin's observation that `a(n) mod n` only decreases until it wraps around.
-/

namespace Recaman

/-- The level: `a n div n`. -/
def lev (n : Nat) : Nat := a n / n
/-- The offset: `a n mod n`. -/
def off (n : Nat) : Nat := a n % n

theorem decomp (n : Nat) : a n = lev n * n + off n := by
  unfold lev off; rw [Nat.mul_comm]; exact (Nat.div_add_mod (a n) n).symm

theorem off_lt {n : Nat} (hn : 0 < n) : off n < n := Nat.mod_lt _ hn

/-- Uniqueness of division with remainder. -/
theorem divmod_of {x b d e : Nat} (he : e < b) (hx : x = d * b + e) : x / b = d ∧ x % b = e := by
  subst hx
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt he, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]

/-- `a n ≤ 0 + 1 + ⋯ + n`. -/
theorem a_le_tri (n : Nat) : a n ≤ tri n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show a (n + 1) ≤ tri n + (n + 1)
    rcases step_cases n with e | e <;> omega

theorem two_mul_tri (n : Nat) : 2 * tri n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 2 * (tri n + (n + 1)) = (n + 1) * (n + 1 + 1)
    rw [Nat.mul_add, ih, Nat.mul_comm n (n + 1), Nat.mul_add (n + 1) (n + 1) 1, Nat.mul_add (n + 1) n 1]
    omega

/-- The level never exceeds `n` (in fact `2 * lev n ≤ n + 1`). -/
theorem two_mul_lev_le (n : Nat) : 2 * lev n ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · show 2 * (a 0 / 0) ≤ 1; simp
  · have h1 : lev n * n ≤ a n := by rw [decomp n]; omega
    have h2 : 2 * (lev n * n) ≤ n * (n + 1) := by
      rw [← two_mul_tri]; have := a_le_tri n; omega
    have h3 : (2 * lev n) * n ≤ (n + 1) * n := by
      rw [Nat.mul_assoc, Nat.mul_comm (n + 1)]; exact h2
    exact Nat.le_of_mul_le_mul_right h3 hn

theorem lev_le (n : Nat) : lev n ≤ n := by have := two_mul_lev_le n; omega

/-! ## The four cases of a step -/

/-- Forward step, no wrap: level `+1`, offset `- lev`. -/
theorem clock_fwd {n : Nat} (hn : 1 ≤ n) (hf : ¬ Back n) (h : lev n ≤ off n) :
    lev (n + 1) = lev n + 1 ∧ off (n + 1) = off n - lev n := by
  have e := a_succ_of_not_back hf
  have d := decomp n
  have hl := off_lt (show 0 < n by omega)
  have := divmod_of (x := a (n + 1)) (b := n + 1) (d := lev n + 1) (e := off n - lev n)
    (by omega) (by rw [e, d, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)
  exact this

/-- Backward step, no wrap: level `-1`, offset `- lev`. -/
theorem clock_back {n : Nat} (hn : 1 ≤ n) (hb : Back n) (h : lev n ≤ off n) :
    lev (n + 1) + 1 = lev n ∧ off (n + 1) = off n - lev n := by
  have e := a_succ_of_back hb
  have h1 := hb.1
  have d := decomp n
  have hl := off_lt (show 0 < n by omega)
  obtain ⟨p, hp⟩ : ∃ p, lev n = p + 1 := by
    rcases Nat.eq_zero_or_pos (lev n) with h0 | h0
    · rw [h0] at d; omega
    · exact ⟨lev n - 1, by omega⟩
  rw [hp] at d h ⊢
  have := divmod_of (x := a (n + 1)) (b := n + 1) (d := p) (e := off n - (p + 1))
    (by omega) (by rw [e, d, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega)
  exact ⟨by unfold lev; omega, this.2⟩

/-- Forward step at a wrap: level unchanged, offset jumps up by `n + 1 - lev`. -/
theorem clock_fwd_wrap {n : Nat} (_hn : 1 ≤ n) (hf : ¬ Back n) (h : off n < lev n) :
    lev (n + 1) = lev n ∧ off (n + 1) = n + 1 + off n - lev n := by
  have e := a_succ_of_not_back hf
  have d := decomp n
  have hq := lev_le n
  have := divmod_of (x := a (n + 1)) (b := n + 1) (d := lev n) (e := n + 1 + off n - lev n)
    (by omega) (by rw [e, d, Nat.mul_add, Nat.mul_one]; omega)
  exact this

/-- Backward step at a wrap: level `-2`, offset jumps up by `n + 1 - lev`. -/
theorem clock_back_wrap {n : Nat} (hn : 1 ≤ n) (hb : Back n) (h : off n < lev n) :
    lev (n + 1) + 2 = lev n ∧ off (n + 1) = n + 1 + off n - lev n := by
  have e := a_succ_of_back hb
  have h1 := hb.1
  have d := decomp n
  have hq := lev_le n
  have hl := off_lt (show 0 < n by omega)
  obtain ⟨p, hp⟩ : ∃ p, lev n = p + 2 := by
    rcases Nat.lt_or_ge (lev n) 2 with h0 | h0
    · have : lev n * n ≤ n := by
        rcases (by omega : lev n = 0 ∨ lev n = 1) with h' | h' <;> rw [h'] <;> omega
      omega
    · exact ⟨lev n - 2, by omega⟩
  rw [hp] at d h hq ⊢
  have := divmod_of (x := a (n + 1)) (b := n + 1) (d := p) (e := n + 1 + off n - (p + 2))
    (by omega) (by rw [e, d, Nat.add_mul, Nat.mul_add, Nat.mul_one]; omega)
  exact ⟨by unfold lev; omega, this.2⟩

/-- `Wrap n`: step `n + 1` wraps the offset around. -/
def Wrap (n : Nat) : Prop := off n < lev n

instance (n : Nat) : Decidable (Wrap n) := by unfold Wrap; infer_instance

/-- Without a wrap the offset drops by exactly the level. -/
theorem off_succ {n : Nat} (hn : 1 ≤ n) (h : ¬ Wrap n) : off (n + 1) + lev n = off n := by
  unfold Wrap at h
  by_cases hb : Back n
  · have := clock_back hn hb (by omega); omega
  · have := clock_fwd hn hb (by omega); omega

/-- A wrap is exactly a step at which the offset goes up. -/
theorem wrap_iff {n : Nat} (hn : 1 ≤ n) : Wrap n ↔ off n < off (n + 1) := by
  constructor
  · intro h
    have hq := lev_le n
    by_cases hb : Back n
    · have := clock_back_wrap hn hb h; omega
    · have := clock_fwd_wrap hn hb h; omega
  · intro h
    apply Classical.byContradiction
    intro hw
    have := off_succ hn hw
    omega

/-- At level 0 the walk must step forward, to level 1. -/
theorem lev_succ_of_lev_zero {n : Nat} (hn : 1 ≤ n) (h : lev n = 0) : lev (n + 1) = 1 := by
  have d := decomp n
  have hl := off_lt (show 0 < n by omega)
  have hf : ¬ Back n := fun hb => by have := hb.1; rw [h] at d; omega
  have := clock_fwd hn hf (by omega)
  omega

/-- **Wraps never stop**: one occurs in every stretch from `n` to `3n`. -/
theorem wrap_between {n : Nat} (hn : 1 ≤ n) : ∃ m, n ≤ m ∧ m < 3 * n ∧ Wrap m := by
  apply Classical.byContradiction
  intro hcon
  have nw : ∀ m, n ≤ m → m < 3 * n → ¬ Wrap m := fun m h1 h2 hw => hcon ⟨m, h1, h2, hw⟩
  have key : ∀ j, j ≤ n → off (n + 2 * j) + j ≤ off n := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      have e1 := off_succ (n := n + 2 * j) (by omega) (nw _ (by omega) (by omega))
      have e2 := off_succ (n := n + 2 * j + 1) (by omega) (nw _ (by omega) (by omega))
      have pos : 1 ≤ lev (n + 2 * j) + lev (n + 2 * j + 1) := by
        rcases Nat.eq_zero_or_pos (lev (n + 2 * j)) with h0 | h0
        · have := lev_succ_of_lev_zero (n := n + 2 * j) (by omega) h0; omega
        · omega
      rw [show n + 2 * (j + 1) = n + 2 * j + 1 + 1 by omega]
      omega
  have := key n (Nat.le_refl n)
  have := off_lt (show 0 < n by omega)
  omega

theorem wrap_infinitely_often (N : Nat) : ∃ m, N ≤ m ∧ Wrap m := by
  obtain ⟨m, h1, _, h3⟩ := wrap_between (n := N + 1) (by omega)
  exact ⟨m, by omega, h3⟩

/-- Between wraps the offset never increases. -/
theorem off_antitone {i j : Nat} (hi : 1 ≤ i) (hij : i ≤ j)
    (nw : ∀ m, i ≤ m → m < j → ¬ Wrap m) : off j ≤ off i := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
    have := ih (by omega) (fun m h1 h2 => nw m h1 (by omega))
    have := off_succ (n := i + d) (by omega) (nw _ (by omega) (by omega))
    rw [show i + (d + 1) = i + d + 1 by omega]
    omega

/-- **Chaffin's monotonicity, exactly.** Between two wraps, each term below the diagonal is
at most every earlier term below the diagonal. So the smallest term of a pass is its last
term below the diagonal: a *landing*. -/
theorem below_diag_antitone {i j : Nat} (hi : 1 ≤ i) (hij : i ≤ j)
    (nw : ∀ m, i ≤ m → m < j → ¬ Wrap m) (hai : a i < i) (haj : a j < j) : a j ≤ a i := by
  have h1 : a i = off i := by unfold off; rw [Nat.mod_eq_of_lt hai]
  have h2 : a j = off j := by unfold off; rw [Nat.mod_eq_of_lt haj]
  rw [h1, h2]; exact off_antitone hi hij nw

/-- **Holes are filled from level 1.** Late enough, step `n + 1` lands on a new number `y`
exactly when the walk is at level 1 with offset `y + 1`. -/
theorem fill_iff {n y : Nat} (hy : y + 1 < n) :
    (a (n + 1) = y ∧ ¬ Visited n y) ↔ (lev n = 1 ∧ off n = y + 1 ∧ 0 < y ∧ ¬ Visited n y) := by
  constructor
  · rintro ⟨e, hv⟩
    rcases back_or_fwd n with ⟨hb, e'⟩ | ⟨_, e'⟩
    · have hpos := (back_new hb).1
      have := divmod_of (x := a n) (b := n) (d := 1) (e := y + 1) (by omega) (by omega)
      exact ⟨this.1, this.2, by omega, hv⟩
    · omega
  · rintro ⟨h1, h2, hy0, hv⟩
    have d := decomp n
    rw [h1, h2, Nat.one_mul] at d
    have hb : Back n := ⟨by omega, by rwa [show a n - (n + 1) = y by omega]⟩
    exact ⟨by rw [a_succ_of_back hb]; omega, hv⟩

end Recaman
