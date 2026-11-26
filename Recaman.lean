/-!
# Recamán's sequence and Sloane's conjecture

OEIS A005132: `a 0 = 0`, and `a (n+1) = a n - (n+1)` if that number is positive and has not
occurred among `a 0, …, a n`; otherwise `a (n+1) = a n + (n+1)`:

  0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9, 24, 8, 25, 43, 62, 42, 63, 41, 18, 42, …

**Sloane's conjecture** (1991): every natural number occurs. It is open. This file states it,
proves an exact reformulation, and proves the structural facts that any proof or disproof has to
work with: zigzags, jumps, transitions, the top-down cascades by which small numbers get filled,
the "ladder" bookkeeping, and a "window theorem" describing exactly how a missing number such as
852655 could still appear.

Core Lean 4 only: no Mathlib, no `sorry`, no `native_decide`, no axioms beyond Lean's standard
three (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Recaman

/-! ## Definition -/

/-- The state after `n` steps: the current term and every term so far, newest first. -/
structure State where
  cur : Nat
  seen : List Nat

/-- Take a step of size `k`: go back if the target is positive and new, else go forward. -/
def State.step (s : State) (k : Nat) : State :=
  if k < s.cur ∧ s.cur - k ∉ s.seen then ⟨s.cur - k, (s.cur - k) :: s.seen⟩
  else ⟨s.cur + k, (s.cur + k) :: s.seen⟩

/-- The state after `n` steps. -/
def state : Nat → State
  | 0 => ⟨0, [0]⟩
  | n + 1 => (state n).step (n + 1)

/-- Recamán's sequence. -/
def a (n : Nat) : Nat := (state n).cur

/-- `Visited n x`: the number `x` is one of `a 0, …, a n`. -/
def Visited (n x : Nat) : Prop := ∃ i, i ≤ n ∧ a i = x

/-- **Sloane's conjecture**: every natural number occurs in Recamán's sequence. (Open.) -/
def SloaneConjecture : Prop := ∀ m : Nat, ∃ n, a n = m

/-! ## The recurrence -/

theorem a_zero : a 0 = 0 := rfl

theorem seen_succ (n : Nat) : (state (n + 1)).seen = a (n + 1) :: (state n).seen := by
  simp only [a, state, State.step]
  by_cases h : n + 1 < (state n).cur ∧ (state n).cur - (n + 1) ∉ (state n).seen
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]

theorem mem_seen (n x : Nat) : x ∈ (state n).seen ↔ Visited n x := by
  induction n with
  | zero =>
    show x ∈ [0] ↔ Visited 0 x
    rw [List.mem_singleton]
    constructor
    · intro h
      exact ⟨0, Nat.le_refl 0, h.symm⟩
    · rintro ⟨i, hi, hx⟩
      have : i = 0 := by omega
      subst this
      exact hx.symm
  | succ n ih =>
    rw [seen_succ, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨i, hi, hx⟩)
      · exact ⟨n + 1, Nat.le_refl _, h.symm⟩
      · exact ⟨i, by omega, hx⟩
    · rintro ⟨i, hi, hx⟩
      by_cases hin : i = n + 1
      · subst hin
        exact Or.inl hx.symm
      · exact Or.inr ⟨i, by omega, hx⟩

instance (n x : Nat) : Decidable (Visited n x) := decidable_of_iff _ (mem_seen n x)

theorem visited_self (n : Nat) : Visited n (a n) := ⟨n, Nat.le_refl n, rfl⟩

theorem Visited.mono {n n' x : Nat} (hv : Visited n x) (h : n ≤ n') : Visited n' x := by
  obtain ⟨i, hi, hx⟩ := hv
  exact ⟨i, by omega, hx⟩

/-- `Back n`: step `n+1` goes backward. -/
def Back (n : Nat) : Prop := n + 1 < a n ∧ ¬ Visited n (a n - (n + 1))

instance (n : Nat) : Decidable (Back n) := by unfold Back; infer_instance

theorem a_succ_of_back {n : Nat} (h : Back n) : a (n + 1) = a n - (n + 1) := by
  show ((state n).step (n + 1)).cur = (state n).cur - (n + 1)
  unfold State.step
  have hc : n + 1 < (state n).cur ∧ (state n).cur - (n + 1) ∉ (state n).seen :=
    ⟨h.1, fun hm => h.2 ((mem_seen _ _).1 hm)⟩
  rw [ite_eq_left hc]

theorem a_succ_of_not_back {n : Nat} (h : ¬ Back n) : a (n + 1) = a n + (n + 1) := by
  show ((state n).step (n + 1)).cur = (state n).cur + (n + 1)
  unfold State.step
  have hc : ¬ (n + 1 < (state n).cur ∧ (state n).cur - (n + 1) ∉ (state n).seen) :=
    fun hc => h ⟨hc.1, fun hv => hc.2 ((mem_seen _ _).2 hv)⟩
  rw [ite_eq_right hc]

theorem back_or_fwd (n : Nat) :
    (Back n ∧ a (n + 1) + (n + 1) = a n) ∨ (¬ Back n ∧ a (n + 1) = a n + (n + 1)) := by
  by_cases h : Back n
  · have e := a_succ_of_back h
    have h1 := h.1
    exact Or.inl ⟨h, by omega⟩
  · exact Or.inr ⟨h, a_succ_of_not_back h⟩

/-- Every step moves by exactly the step size. -/
theorem step_cases (n : Nat) : a (n + 1) + (n + 1) = a n ∨ a (n + 1) = a n + (n + 1) := by
  rcases back_or_fwd n with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem back_iff (n : Nat) : Back n ↔ a (n + 1) < a n := by
  rcases back_or_fwd n with ⟨h, e⟩ | ⟨h, e⟩
  · exact ⟨fun _ => by omega, fun _ => h⟩
  · exact ⟨fun hb => absurd hb h, fun hl => by exfalso; omega⟩

/-- A backward step lands on a positive number that has not occurred before. -/
theorem back_new {n : Nat} (h : Back n) : 0 < a (n + 1) ∧ ¬ Visited n (a (n + 1)) := by
  rw [a_succ_of_back h]
  exact ⟨by have := h.1; omega, h.2⟩

/-- Index-shifted forms, convenient when the time is a compound expression. -/
theorem step_cases' {k t : Nat} (h : k + 1 = t) : a t + t = a k ∨ a t = a k + t := by
  subst h; exact step_cases k

theorem back_iff' {k t : Nat} (h : k + 1 = t) : Back k ↔ a t < a k := by
  subst h; exact back_iff k

/-- Once `v` has occurred, the walk never stands on it again at a later time `t > v`
(a backward step only lands on new numbers; a forward step to time `t` lands at `≥ t`). -/
theorem ne_of_visited {s t v : Nat} (hst : s < t) (hvt : v < t) (hv : Visited s v) :
    a t ≠ v := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  intro he
  rcases back_or_fwd k with ⟨hb, _⟩ | ⟨_, e⟩
  · exact (back_new hb).2 (by rw [he]; exact hv.mono (by omega))
  · omega

/-! ## Elementary facts -/

theorem a_pos {n : Nat} (hn : 0 < n) : 0 < a n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases back_or_fwd k with ⟨h, _⟩ | ⟨_, e⟩
  · exact (back_new h).1
  · omega

/-- Of two consecutive terms, one is at least the step size. -/
theorem le_max_succ (n : Nat) : n + 1 ≤ a n ∨ n + 1 ≤ a (n + 1) := by
  rcases step_cases n with e | e <;> omega

theorem unbounded (M : Nat) : ∃ n, M ≤ a n := by
  rcases le_max_succ M with h | h
  · exact ⟨M, by omega⟩
  · exact ⟨M + 1, by omega⟩

/-- The first 25 terms. -/
theorem first_terms : (List.range 25).map a =
    [0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9, 24, 8, 25, 43, 62, 42, 63, 41, 18,
      42] := by
  decide +kernel

/-- The sequence is not injective: `a 20 = a 24 = 42`. -/
theorem not_injective : ∃ i j, i ≠ j ∧ a i = a j :=
  ⟨20, 24, by decide, by decide +kernel⟩

/-- Triangular numbers. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

/-- Since `-k ≡ k (mod 2)`, every term has the parity of `0 + 1 + ⋯ + n`. -/
theorem a_mod_two_eq_tri (n : Nat) : a n % 2 = tri n % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show a (n + 1) % 2 = (tri n + (n + 1)) % 2
    rcases step_cases n with e | e <;> omega

theorem tri_mod_two (n : Nat) : tri n % 2 = if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (tri n + (n + 1)) % 2 = _
    split <;> split at ih <;> omega

/-- **Parity law.** `a n` is odd exactly when `n ≡ 1` or `2 (mod 4)`. -/
theorem a_mod_two (n : Nat) : a n % 2 = if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0 := by
  rw [a_mod_two_eq_tri, tri_mod_two]

/-! ## An exact reformulation of the conjecture -/

/-- `m` occurs iff it is among the first `m + 1` terms or, at some time `k`, the walk stands
exactly `m + 1` above the diagonal: `a k = k + m + 1`. -/
theorem occurs_iff (m : Nat) : (∃ n, a n = m) ↔ Visited m m ∨ ∃ k, a k = k + m + 1 := by
  constructor
  · rintro ⟨n, hn⟩
    by_cases hnm : n ≤ m
    · exact Or.inl ⟨n, hnm, hn⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact Or.inr ⟨k, by rcases step_cases k with e | e <;> omega⟩
  · rintro (⟨i, _, hi⟩ | ⟨k, hk⟩)
    · exact ⟨i, hi⟩
    · by_cases hv : Visited k m
      · obtain ⟨i, _, hi⟩ := hv
        exact ⟨i, hi⟩
      · by_cases hm : m = 0
        · exact ⟨0, by rw [hm]; rfl⟩
        · have hb : Back k := ⟨by omega, by rwa [show a k - (k + 1) = m by omega]⟩
          exact ⟨k + 1, by rw [a_succ_of_back hb]; omega⟩

/-- Sloane's conjecture says the height above the diagonal, `a k - k`, eventually takes every
needed value *exactly*. -/
theorem sloane_iff : SloaneConjecture ↔ ∀ m, Visited m m ∨ ∃ k, a k = k + m + 1 :=
  ⟨fun h m => (occurs_iff m).1 (h m), fun h m => (occurs_iff m).2 (h m)⟩

/-! ## Zigzags -/

/-- **Zigzag lemma.** Suppose `a k = x`, the numbers `x - 1, …, x - r` are still free at time
`k`, and the first `r` jump tests fail (each tested number `x - j - (k + 2j + 1)` is not above
the diagonal or has already occurred). Then the walk alternates `x, x+k+1, x-1, x+k+2, …, x-r`,
filling the free run below `x` from the top, one number every two steps. -/
theorem zigzag {k x r : Nat} (hx : a k = x) (hr : r < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ r → ¬ Visited k (x - i))
    (htest : ∀ j, j < r → k + 2 * j + 1 < x - j → Visited k (x - j - (k + 2 * j + 1))) :
    ∀ j, j ≤ r → a (k + 2 * j) = x - j ∧ ∀ t, k < t → t ≤ k + 2 * j → x - j ≤ a t := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨by simpa using hx, fun t h1 h2 => by omega⟩
  | succ j ih =>
    intro hj
    obtain ⟨h0, hlow⟩ := ih (by omega)
    -- step k+2j+1: the jump test fails, so the walk goes up
    have hnb : ¬ Back (k + 2 * j) := by
      intro hb
      apply hb.2
      have h1 := hb.1
      rw [h0] at h1 ⊢
      exact (htest j (by omega) h1).mono (by omega)
    have e1 : a (k + 2 * j + 1) = x + k + 1 + j := by
      rw [a_succ_of_not_back hnb, h0]; omega
    -- step k+2j+2: x-(j+1) is still free, so the walk comes back down onto it
    have hnv : ¬ Visited (k + 2 * j + 1) (x - (j + 1)) := by
      rintro ⟨i, hi, hai⟩
      by_cases hik : i ≤ k
      · exact hfree (j + 1) (by omega) hj ⟨i, hik, hai⟩
      · by_cases hi' : i ≤ k + 2 * j
        · have := hlow i (by omega) hi'
          omega
        · have : i = k + 2 * j + 1 := by omega
          subst this
          omega
    have hb : Back (k + 2 * j + 1) := by
      refine ⟨by rw [e1]; omega, ?_⟩
      rw [e1, show x + k + 1 + j - (k + 2 * j + 1 + 1) = x - (j + 1) by omega]
      exact hnv
    have e2 : a (k + 2 * (j + 1)) = x - (j + 1) := by
      rw [show k + 2 * (j + 1) = k + 2 * j + 1 + 1 by omega, a_succ_of_back hb, e1]
      omega
    refine ⟨e2, fun t h1 h2 => ?_⟩
    by_cases ht : t ≤ k + 2 * j
    · have := hlow t h1 ht
      omega
    · by_cases ht' : t = k + 2 * j + 1
      · subst ht'; omega
      · have : t = k + 2 * (j + 1) := by omega
        subst this; omega

/-- The upper branch of a zigzag: `a (k + 2j + 1) = x + k + 1 + j`. -/
theorem zigzag_odd {k x r : Nat} (hx : a k = x) (hr : r < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ r → ¬ Visited k (x - i))
    (htest : ∀ j, j < r → k + 2 * j + 1 < x - j → Visited k (x - j - (k + 2 * j + 1)))
    (j : Nat) (hj : j < r) : a (k + 2 * j + 1) = x + k + 1 + j := by
  have h0 := (zigzag hx hr hfree htest j (by omega)).1
  have h2 := (zigzag hx hr hfree htest (j + 1) (by omega)).1
  rcases step_cases (k + 2 * j) with e | e <;>
    rcases step_cases' (show k + 2 * j + 1 + 1 = k + 2 * (j + 1) by omega) with f | f <;>
    omega

/-- Below the diagonal (`x ≤ k + 1`) no jump test can succeed, so a free run below `x` is
always filled completely. -/
theorem zigzag_below {k x r : Nat} (hx : a k = x) (hxk : x ≤ k + 1) (hr : r < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ r → ¬ Visited k (x - i)) (j : Nat) (hj : j ≤ r) :
    a (k + 2 * j) = x - j :=
  (zigzag hx hr hfree (fun j _ h => absurd h (by omega)) j hj).1

/-! ## Transitions: how a finished zigzag restarts the walk two levels up -/

/-- **Transition lemma.** Suppose step `s` went backward to `a s = ℓ`, the jump test at step
`s+1` fails, and `ℓ - 1` has already occurred (the free run below `ℓ` is used up). Then the next
three steps go forward, and if `ℓ + 2s + 2` is still free the walk lands on it:
`a (s+4) = 2 (s+4) + (ℓ - 6)`. So draining a hole down to `ℓ` restarts the walk just above
`2t` with offset `ℓ - 6`; its jump tests then sit `ℓ - 8, ℓ - 13, …` above the diagonal, and a
landing there scans the numbers just below `ℓ`. This is why holes tend to be filled top-down. -/
theorem transition {s ℓ : Nat} (hs1 : 1 ≤ s) (hs : a s = ℓ) (hback : Back (s - 1))
    (htest : ¬ Back s) (hprev : 1 ≤ ℓ → Visited s (ℓ - 1))
    (hnew : ¬ Visited s (ℓ + 2 * s + 2)) :
    a (s + 1) = ℓ + s + 1 ∧ a (s + 2) = ℓ + 2 * s + 3 ∧ a (s + 3) = ℓ + 3 * s + 6 ∧
      a (s + 4) = ℓ + 2 * s + 2 := by
  have hprevs : a (s - 1) = ℓ + s := by
    have e := a_succ_of_back hback
    have h1 := hback.1
    rw [show s - 1 + 1 = s by omega] at e
    omega
  have e1 : a (s + 1) = ℓ + s + 1 := by rw [a_succ_of_not_back htest, hs]; omega
  have nb1 : ¬ Back (s + 1) := by
    intro hb
    have h1 := hb.1
    apply hb.2
    rw [e1, show ℓ + s + 1 - (s + 1 + 1) = ℓ - 1 by omega]
    exact (hprev (by omega)).mono (by omega)
  have e2 : a (s + 2) = ℓ + 2 * s + 3 := by
    have h : a (s + 2) = a (s + 1) + (s + 2) := a_succ_of_not_back nb1
    omega
  have nb2 : ¬ Back (s + 2) := by
    intro hb
    apply hb.2
    rw [e2, show ℓ + 2 * s + 3 - (s + 2 + 1) = ℓ + s by omega, ← hprevs]
    exact (visited_self (s - 1)).mono (by omega)
  have e3 : a (s + 3) = ℓ + 3 * s + 6 := by
    have h : a (s + 3) = a (s + 2) + (s + 3) := a_succ_of_not_back nb2
    omega
  have hb3 : Back (s + 3) := by
    refine ⟨by rw [e3]; omega, ?_⟩
    rw [e3, show ℓ + 3 * s + 6 - (s + 3 + 1) = ℓ + 2 * s + 2 by omega]
    rintro ⟨i, hi, hai⟩
    by_cases his : i ≤ s
    · exact hnew ⟨i, his, hai⟩
    · have : i = s + 1 ∨ i = s + 2 ∨ i = s + 3 := by omega
      rcases this with rfl | rfl | rfl <;> omega
  have e4 : a (s + 4) = a (s + 3) - (s + 4) := a_succ_of_back hb3
  exact ⟨e1, e2, e3, by omega⟩

/-- **Jump lemma.** If the first `j` jump tests of a zigzag fail, the free run below `x` has
length at least `j`, and the `j`-th tested number is positive and free, then the walk jumps
onto it: `a (k + 2j + 1) = x - k - 1 - 3j`. -/
theorem zigzag_jump {k x j : Nat} (hx : a k = x) (hj : j < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ j → ¬ Visited k (x - i))
    (htest : ∀ i, i < j → k + 2 * i + 1 < x - i → Visited k (x - i - (k + 2 * i + 1)))
    (hpos : k + 2 * j + 1 < x - j) (hnew : ¬ Visited k (x - j - (k + 2 * j + 1))) :
    a (k + 2 * j + 1) = x - j - (k + 2 * j + 1) := by
  obtain ⟨e, hlow⟩ := zigzag hx hj hfree htest j (Nat.le_refl j)
  have hb : Back (k + 2 * j) := by
    refine ⟨by omega, ?_⟩
    rw [e]
    rintro ⟨i, hi, hai⟩
    by_cases hik : i ≤ k
    · exact hnew ⟨i, hik, hai⟩
    · have := hlow i (by omega) hi
      omega
  rw [a_succ_of_back hb, e]

/-- **Cascade lemma.** After the transition of `transition` (a zigzag drained down to `ℓ` at
step `s`), the new zigzag at `ℓ + 2s + 2` tests the numbers `ℓ + s - 3 - 3i`. If the `j`-th
test is the first free one (and the free run allows it), the walk jumps onto it at step
`t = s + 5 + 2j`, landing exactly `ℓ - 8 - 5j` above the diagonal: `a t + 5j + 8 = t + ℓ`.
The zigzag that starts there tests `ℓ - 9 - 5j, ℓ - 12 - 5j, …`, which are the numbers just
below `ℓ` in the residue class `(ℓ + j) mod 3` (`cascade_class`). This is how filling one hole
sets up the scan for the next hole below it. -/
theorem cascade {s ℓ j : Nat} (hs1 : 1 ≤ s) (hs : a s = ℓ) (hback : Back (s - 1))
    (htest0 : ¬ Back s) (hprev : 1 ≤ ℓ → Visited s (ℓ - 1))
    (hnew : ¬ Visited s (ℓ + 2 * s + 2))
    (hfree : ∀ i, 1 ≤ i → i ≤ j → ¬ Visited (s + 4) (ℓ + 2 * s + 2 - i))
    (htests : ∀ i, i < j → Visited (s + 4) (ℓ + s - 3 - 3 * i))
    (hpos : 3 * j + 4 ≤ ℓ + s) (hjnew : ¬ Visited (s + 4) (ℓ + s - 3 - 3 * j)) :
    a (s + 5 + 2 * j) + 5 * j + 8 = (s + 5 + 2 * j) + ℓ := by
  obtain ⟨-, -, -, e4⟩ := transition hs1 hs hback htest0 hprev hnew
  have hjump := zigzag_jump (k := s + 4) (x := ℓ + 2 * s + 2) (j := j) e4 (by omega) hfree
    (fun i hi h => by
      rw [show ℓ + 2 * s + 2 - i - (s + 4 + 2 * i + 1) = ℓ + s - 3 - 3 * i by omega]
      exact htests i hi)
    (by omega)
    (by rw [show ℓ + 2 * s + 2 - j - (s + 4 + 2 * j + 1) = ℓ + s - 3 - 3 * j by omega]
        exact hjnew)
  rw [show s + 5 + 2 * j = s + 4 + 2 * j + 1 by omega, hjump]
  omega

/-- The residue class scanned after a cascade step: `ℓ - 9 - 5j ≡ ℓ + j (mod 3)`. -/
theorem cascade_class (ℓ j : Nat) (h : 9 + 5 * j ≤ ℓ) : (ℓ - 9 - 5 * j) % 3 = (ℓ + j) % 3 := by
  omega

/-! ## Ladder offsets

Measure the walk against the lines `L · t` for integer levels `L`, writing `a t = L t + δ`. A jump
moves one level down and shifts the offset by exactly `-L`. A transition moves two levels up and
shifts it by `-(4L + 6)`. Each round of a zigzag moves the lower branch's offset by `-(2L + 1)`.
So jumps and transitions keep the walk on one family of lines `(L + c) t` up to bounded shifts,
and only zigzag rounds change `c`. This is the "ladder" seen in the computations: the walk can
reach small numbers only when `c` is very close to an integer. -/

/-- A backward step moves one level down: the offset relative to `L t` drops by exactly `L`. -/
theorem ladder_back {k : Nat} (h : Back k) (L : Int) :
    (a (k + 1) : Int) - (L - 1) * ((k + 1 : Nat) : Int) = ((a k : Int) - L * k) - L := by
  have e := a_succ_of_back h
  have h1 := h.1
  have e' : (a (k + 1) : Int) = (a k : Int) - ((k : Int) + 1) := by omega
  have hk : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
  rw [e', hk]
  grind

/-- A transition (`transition`) moves two levels up: the offset drops by exactly `4L + 6`. -/
theorem ladder_transition {s ℓ : Nat} (hs1 : 1 ≤ s) (hs : a s = ℓ) (hback : Back (s - 1))
    (htest : ¬ Back s) (hprev : 1 ≤ ℓ → Visited s (ℓ - 1))
    (hnew : ¬ Visited s (ℓ + 2 * s + 2)) (L : Int) :
    (a (s + 4) : Int) - (L + 2) * ((s + 4 : Nat) : Int) =
      ((a s : Int) - L * s) - 4 * L - 6 := by
  obtain ⟨-, -, -, e4⟩ := transition hs1 hs hback htest hprev hnew
  have e4' : (a (s + 4) : Int) = (a s : Int) + 2 * (s : Int) + 2 := by omega
  have hs4 : ((s + 4 : Nat) : Int) = (s : Int) + 4 := by omega
  rw [e4', hs4]
  grind

/-- Along a zigzag's lower branch (`zigzag`), each round lowers the offset by `2L + 1`. -/
theorem ladder_zigzag {k x r : Nat} (hx : a k = x) (hr : r < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ r → ¬ Visited k (x - i))
    (htest : ∀ j, j < r → k + 2 * j + 1 < x - j → Visited k (x - j - (k + 2 * j + 1)))
    (j : Nat) (hj : j ≤ r) (L : Int) :
    (a (k + 2 * j) : Int) - L * ((k + 2 * j : Nat) : Int) =
      ((x : Int) - L * k) - (2 * L + 1) * j := by
  have e := (zigzag hx hr hfree htest j hj).1
  have e' : (a (k + 2 * j) : Int) = (x : Int) - j := by omega
  have hk : ((k + 2 * j : Nat) : Int) = (k : Int) + 2 * j := by omega
  rw [e', hk]
  grind

/-! ## How the walk enters a gap -/

/-- **Entry lemma.** If step `n+2` goes backward, then either the walk is continuing down a
zigzag (`a n = a (n+2) + 1`), or step `n+1` went backward too and `a n = a (n+2) + 2n + 3`:
a *jump* of two consecutive backward steps. -/
theorem entry {n : Nat} (hb : Back (n + 1)) :
    a n = a (n + 2) + 1 ∨ (Back n ∧ a n = a (n + 2) + 2 * n + 3) := by
  have e2 : a (n + 2) = a (n + 1) - (n + 2) := a_succ_of_back hb
  have h1 : n + 2 < a (n + 1) := hb.1
  rcases back_or_fwd n with ⟨h, e⟩ | ⟨_, e⟩
  · exact Or.inr ⟨h, by omega⟩
  · exact Or.inl (by omega)

/-- Late in the sequence, a number whose upper neighbour has already occurred can only be
reached by a jump. -/
theorem entry_exposed {n y : Nat} (hb : Back (n + 1)) (hy : a (n + 2) = y)
    (hv : Visited (n - 1) (y + 1)) (hlt : y + 1 < n) : Back n ∧ a n = y + 2 * n + 3 := by
  rcases entry hb with h | h
  · exact absurd (by omega : a n = y + 1) (ne_of_visited (by omega) hlt hv)
  · exact ⟨h.1, by omega⟩

/-! ## Both kinds of step occur infinitely often -/

theorem exists_fwd (N : Nat) : ∃ n, N ≤ n ∧ ¬ Back n := by
  apply Classical.byContradiction
  intro hcon
  have hall : ∀ n, N ≤ n → Back n := fun n hn =>
    Classical.byContradiction fun h => hcon ⟨n, hn, h⟩
  have key : ∀ t, a (N + t) + t ≤ a N := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hb := hall (N + t) (by omega)
      have e := a_succ_of_back hb
      have h1 := hb.1
      rw [show N + (t + 1) = N + t + 1 by omega, e]
      omega
  have := key (a N + 1)
  omega

theorem bounded_prefix (N : Nat) : ∃ C, ∀ i, i ≤ N → a i ≤ C := by
  induction N with
  | zero => exact ⟨a 0, fun i hi => by rw [show i = 0 by omega]; exact Nat.le_refl _⟩
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + a (N + 1), fun i hi => ?_⟩
    by_cases h : i ≤ N
    · have := hC i h; omega
    · rw [show i = N + 1 by omega]; omega

theorem exists_back (N : Nat) : ∃ n, N ≤ n ∧ Back n := by
  apply Classical.byContradiction
  intro hcon
  have fwd : ∀ n, N ≤ n → a (n + 1) = a n + (n + 1) :=
    fun n hn => a_succ_of_not_back fun hb => hcon ⟨n, hn, hb⟩
  have mono : ∀ t i, N ≤ i → a i ≤ a (i + t) := by
    intro t
    induction t with
    | zero => intro i _; simp
    | succ t ih =>
      intro i hi
      have h1 := ih i hi
      have h2 := fwd (i + t) (by omega)
      rw [show i + (t + 1) = i + t + 1 by omega]
      omega
  have grow : ∀ t, a N + t ≤ a (N + t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h2 := fwd (N + t) (by omega)
      rw [show N + (t + 1) = N + t + 1 by omega]
      omega
  obtain ⟨C, hC⟩ := bounded_prefix N
  obtain ⟨n, hn⟩ : ∃ n, n = N + C + 3 := ⟨_, rfl⟩
  have hg : a N + (C + 3) ≤ a n := by
    have := grow (C + 3); rwa [show N + (C + 3) = n by omega] at this
  have hn0 : a n = a (n - 1) + n := by
    have := fwd (n - 1) (by omega); rwa [show n - 1 + 1 = n by omega] at this
  have hn1 := fwd n (by omega)
  -- step n+2 is forward, so its jump target `a n - 1` must already have occurred ...
  have hv : Visited (n + 1) (a n - 1) := by
    apply Classical.byContradiction
    intro hnv
    apply hcon
    refine ⟨n + 1, by omega, ?_⟩
    refine ⟨by omega, ?_⟩
    rw [hn1, show a n + (n + 1) - (n + 1 + 1) = a n - 1 by omega]
    exact hnv
  -- ... but no term up to time n+1 equals `a n - 1`.
  obtain ⟨i, hi, hai⟩ := hv
  by_cases h1 : i ≤ N
  · have := hC i h1; omega
  · by_cases h2 : i ≤ n - 1
    · have := mono (n - 1 - i) i (by omega)
      rw [show i + (n - 1 - i) = n - 1 by omega] at this
      omega
    · by_cases h3 : i = n
      · subst h3; omega
      · have : i = n + 1 := by omega
        subst this; omega

/-! ## The window theorem

Suppose that by time `N` every number strictly between `m` and `m'` has occurred, where
`m < m'` and `m ≡ m' (mod 3)`. Then `m` can appear later only in one way: a jump lands
exactly `m + 1 + 3j` above the diagonal (for some `j` with `m + 1 + 3j ≤ m' - 2`), and the
zigzag that follows walks its jump tests `m + 3j, …, m + 3, m` down to `m`. Conversely, such
a landing with a free run below it does produce `m`. -/

theorem window {m m' N n : Nat} (hlt : m < m') (hmod : m' % 3 = m % 3) (hN : m' ≤ N)
    (hfill : ∀ v, m < v → v < m' → Visited N v) (hfree : ¬ Visited (n - 1) m')
    (hn : N + (m' - m) + 4 ≤ n) (ha : a n = m) :
    ∃ j, 3 * (j + 1) ≤ m' - m ∧ (∀ i, i ≤ j → a (n - 1 - 2 * i) = m + n + i) ∧
      Back (n - 2 - 2 * j) ∧ Back (n - 3 - 2 * j) := by
  -- the last step lands on `m` from `m + n`
  have h0 : a (n - 1) = m + n := by
    rcases step_cases' (show n - 1 + 1 = n by omega) with e | e <;> omega
  -- after time `N` the walk never stands on a number strictly between `m` and `m'`
  have nostand : ∀ t v, N < t → m < v → v < m' → a t ≠ v := fun t v ht h1 h2 =>
    ne_of_visited ht (by omega) (hfill v h1 h2)
  -- one step of reading the zigzag backwards
  have step : ∀ i, (3 * i < m' - m ∧ (∀ i', i' ≤ i → a (n - 1 - 2 * i') = m + n + i') ∧
        Back (n - 2 - 2 * i)) →
      (3 * (i + 1) ≤ m' - m ∧ (∀ i', i' ≤ i → a (n - 1 - 2 * i') = m + n + i') ∧
        Back (n - 2 - 2 * i) ∧ Back (n - 3 - 2 * i)) ∨
      (3 * (i + 1) < m' - m ∧ (∀ i', i' ≤ i + 1 → a (n - 1 - 2 * i') = m + n + i') ∧
        Back (n - 2 - 2 * (i + 1))) := by
    intro i ⟨hi3, hchain, hback⟩
    have hval := hchain i (Nat.le_refl i)
    have hrel : a (n - 1 - 2 * i) + (n - 1 - 2 * i) = a (n - 2 - 2 * i) := by
      have hl := (back_iff' (show n - 2 - 2 * i + 1 = n - 1 - 2 * i by omega)).1 hback
      rcases step_cases' (show n - 2 - 2 * i + 1 = n - 1 - 2 * i by omega) with e | e <;> omega
    by_cases hb3 : Back (n - 3 - 2 * i)
    · exact Or.inl ⟨by omega, hchain, hback, hb3⟩
    · right
      have e3 : a (n - 2 - 2 * i) = a (n - 3 - 2 * i) + (n - 2 - 2 * i) := by
        have := a_succ_of_not_back hb3
        rwa [show n - 3 - 2 * i + 1 = n - 2 - 2 * i by omega] at this
      have hval' : a (n - 3 - 2 * i) = m + n + (i + 1) := by omega
      -- the failed jump test at step n-2-2i was the number m + 3(i+1): it has occurred
      have htest : Visited (n - 3 - 2 * i) (m + 3 * (i + 1)) := by
        apply Classical.byContradiction
        intro hnv
        apply hb3
        refine ⟨by omega, ?_⟩
        rw [show a (n - 3 - 2 * i) - (n - 3 - 2 * i + 1) = m + 3 * (i + 1) by omega]
        exact hnv
      have hne : m + 3 * (i + 1) ≠ m' := fun h => hfree (by rw [← h]; exact htest.mono (by omega))
      -- the step into `a (n-3-2i)` was backward: the walk cannot stand on `m + 4 + 3i`
      have hback' : Back (n - 4 - 2 * i) := by
        apply (back_iff' (show n - 4 - 2 * i + 1 = n - 3 - 2 * i by omega)).2
        rcases step_cases' (show n - 4 - 2 * i + 1 = n - 3 - 2 * i by omega) with e | e
        · omega
        · exfalso
          exact nostand (n - 4 - 2 * i) (m + 4 + 3 * i) (by omega) (by omega) (by omega)
            (by omega)
      refine ⟨by omega, fun i' hi' => ?_, ?_⟩
      · by_cases h : i' ≤ i
        · exact hchain i' h
        · rw [show i' = i + 1 by omega, show n - 1 - 2 * (i + 1) = n - 3 - 2 * i by omega]
          exact hval'
      · rwa [show n - 2 - 2 * (i + 1) = n - 4 - 2 * i by omega]
  have inv0 : 3 * 0 < m' - m ∧ (∀ i', i' ≤ 0 → a (n - 1 - 2 * i') = m + n + i') ∧
      Back (n - 2 - 2 * 0) := by
    refine ⟨by omega, fun i' hi' => ?_, ?_⟩
    · rw [show i' = 0 by omega]; simpa using h0
    · apply (back_iff' (show n - 2 - 2 * 0 + 1 = n - 1 by omega)).2
      rcases step_cases' (show n - 2 - 2 * 0 + 1 = n - 1 by omega) with e | e
      · omega
      · exfalso
        exact nostand (n - 2 - 2 * 0) (m + 1) (by omega) (by omega) (by omega) (by omega)
  have reach : ∀ i, (∃ j, j ≤ i ∧ 3 * (j + 1) ≤ m' - m ∧
        (∀ i', i' ≤ j → a (n - 1 - 2 * i') = m + n + i') ∧
        Back (n - 2 - 2 * j) ∧ Back (n - 3 - 2 * j)) ∨
      (3 * i < m' - m ∧ (∀ i', i' ≤ i → a (n - 1 - 2 * i') = m + n + i') ∧
        Back (n - 2 - 2 * i)) := by
    intro i
    induction i with
    | zero => exact Or.inr inv0
    | succ i ih =>
      rcases ih with ⟨j, hj, hd⟩ | hinv
      · exact Or.inl ⟨j, by omega, hd⟩
      · rcases step i hinv with hd | hinv'
        · exact Or.inl ⟨i, by omega, hd⟩
        · exact Or.inr ⟨by omega, hinv'.2⟩
  rcases reach ((m' - m) / 3) with ⟨j, _, hd⟩ | ⟨h3, _, _⟩
  · exact ⟨j, hd⟩
  · exfalso; omega

/-- **Window theorem, converse.** If at time `t` the walk stands at `t + m + 1 + 3j`, the `j`
numbers just below it are still free, the tested numbers `m + 3, …, m + 3j` have occurred,
and `m ≥ 1` is still missing, then `a (t + 2j + 1) = m`. -/
theorem window_suff {t m j : Nat} (hm : 0 < m) (hL : a t = t + m + 1 + 3 * j)
    (hfreeL : ∀ i, 1 ≤ i → i ≤ j → ¬ Visited t (a t - i))
    (htests : ∀ i, 1 ≤ i → i ≤ j → Visited t (m + 3 * i))
    (hmfree : ¬ Visited t m) : a (t + 2 * j + 1) = m := by
  obtain ⟨e, hlow⟩ := zigzag (k := t) (x := a t) (r := j) rfl (by omega) hfreeL
    (fun i hi _ => by
      rw [show a t - i - (t + 2 * i + 1) = m + 3 * (j - i) by omega]
      exact htests (j - i) (by omega) (by omega)) j (Nat.le_refl j)
  have hb : Back (t + 2 * j) := by
    refine ⟨by omega, ?_⟩
    rw [e, show a t - j - (t + 2 * j + 1) = m by omega]
    rintro ⟨i, hi, hai⟩
    by_cases hit : i ≤ t
    · exact hmfree ⟨i, hit, hai⟩
    · have := hlow i (by omega) hi
      omega
  rw [a_succ_of_back hb, e]
  omega

/-- **The case of 852655.** Chaffin's computation (2018) found that after `10^230` steps the two
smallest missing numbers are `852655` and `930058`, both `≡ 1 (mod 3)`. Taking those facts as
hypotheses (Lean cannot run that computation): if `852655` ever appears, it is because some jump
lands between `852656` and `930056` above the diagonal, at a height `≡ 2 (mod 3)`. -/
theorem window_852655 {N n : Nat} (hN : 930058 ≤ N)
    (hfill : ∀ v, 852655 < v → v < 930058 → Visited N v)
    (hfree : ¬ Visited (n - 1) 930058) (hn : N + 77407 ≤ n) (ha : a n = 852655) :
    ∃ j, 852656 + 3 * j ≤ 930056 ∧
      a (n - 1 - 2 * j) = (n - 1 - 2 * j) + 852656 + 3 * j ∧
      Back (n - 2 - 2 * j) ∧ Back (n - 3 - 2 * j) := by
  obtain ⟨j, hj, hchain, hb2, hb3⟩ :=
    window (m := 852655) (m' := 930058) (N := N) (n := n) (by decide) (by decide) hN hfill
      hfree (by omega) ha
  have := hchain j (Nat.le_refl j)
  exact ⟨j, by omega, by omega, hb2, hb3⟩

/-! ## Small computations, checked by the kernel -/

/-- Every number below 19 occurs within the first 131 terms (4 is the last, at step 131). -/
theorem small_occur : ∀ m, m < 19 → Visited 131 m := by decide +kernel

end Recaman

/-! ## Axiom audit: none of these depend on `sorryAx`. -/
#print axioms Recaman.occurs_iff
#print axioms Recaman.zigzag
#print axioms Recaman.entry_exposed
#print axioms Recaman.exists_back
#print axioms Recaman.a_mod_two
#print axioms Recaman.transition
#print axioms Recaman.zigzag_jump
#print axioms Recaman.cascade
#print axioms Recaman.ladder_back
#print axioms Recaman.ladder_transition
#print axioms Recaman.ladder_zigzag
#print axioms Recaman.window
#print axioms Recaman.window_suff
#print axioms Recaman.window_852655
#print axioms Recaman.small_occur
