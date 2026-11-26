import Recaman
import Recaman.Intervals

/-!
# A verified fast evaluator (phase-level semantics)

A state `⟨n, x, t⟩` stands for "after `n` steps the walk is at `x`, and `t` holds exactly the
numbers visited so far" (`Rep`). `zig` advances one whole zigzag at a time, ending in a jump
when a jump test succeeds; `single` takes one ordinary step. Both are proved to preserve
`Rep`, using the zigzag lemmas of `Recaman.lean`. So `run` computes `a N` and the visited set
correctly, in time roughly proportional to the number of zigzags, not the number of steps.
-/

namespace Recaman

theorem visited_succ (n y : Nat) : Visited (n + 1) y ↔ Visited n y ∨ y = a (n + 1) := by
  constructor
  · rintro ⟨i, hi, hai⟩
    by_cases h : i ≤ n
    · exact Or.inl ⟨i, h, hai⟩
    · exact Or.inr (by rw [← hai, show i = n + 1 by omega])
  · rintro (h | h)
    · exact h.mono (by omega)
    · exact ⟨n + 1, Nat.le_refl _, h.symm⟩

/-- A whole zigzag of `R` rounds, with the visited set it leaves behind. -/
theorem zig_block {k x R : Nat} (hx : a k = x) (hR : R < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ R → ¬ Visited k (x - i))
    (htest : ∀ j, j < R → 3 * j < x - k - 1 → Visited k (x - k - 1 - 3 * j)) :
    a (k + 2 * R) = x - R ∧ ∀ y, Visited (k + 2 * R) y ↔
      Visited k y ∨ (x - R ≤ y ∧ y ≤ x - 1) ∨ (x + k + 1 ≤ y ∧ y ≤ x + k + R) := by
  have ht : ∀ j, j < R → k + 2 * j + 1 < x - j → Visited k (x - j - (k + 2 * j + 1)) :=
    fun j hj h => by
      rw [show x - j - (k + 2 * j + 1) = x - k - 1 - 3 * j by omega]
      exact htest j hj (by omega)
  have ev := zigzag hx hR hfree ht
  have od := zigzag_odd hx hR hfree ht
  refine ⟨(ev R (Nat.le_refl _)).1, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨i, hi, hai⟩
    by_cases hik : i ≤ k
    · exact Or.inl ⟨i, hik, hai⟩
    · obtain ⟨j, hj⟩ : ∃ j, i = k + 2 * j ∨ i = k + 2 * j + 1 := ⟨(i - k) / 2, by omega⟩
      rcases hj with rfl | rfl
      · have := (ev j (by omega)).1; exact Or.inr (Or.inl (by omega))
      · have := od j (by omega); exact Or.inr (Or.inr (by omega))
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono (by omega)
    · refine ⟨k + 2 * (x - y), by omega, ?_⟩
      have := (ev (x - y) (by omega)).1; omega
    · refine ⟨k + 2 * (y - x - k - 1) + 1, by omega, ?_⟩
      have := od (y - x - k - 1) (by omega); omega

/-- A zigzag of `j` rounds that ends with a jump onto `x - k - 1 - 3j`. -/
theorem jump_block {k x j : Nat} (hx : a k = x) (hj : j < x)
    (hfree : ∀ i, 1 ≤ i → i ≤ j → ¬ Visited k (x - i))
    (htest : ∀ i, i < j → 3 * i < x - k - 1 → Visited k (x - k - 1 - 3 * i))
    (hpos : 3 * j < x - k - 1) (hnew : ¬ Visited k (x - k - 1 - 3 * j)) :
    a (k + 2 * j + 1) = x - k - 1 - 3 * j ∧ ∀ y, Visited (k + 2 * j + 1) y ↔
      (Visited k y ∨ (x - j ≤ y ∧ y ≤ x - 1) ∨ (x + k + 1 ≤ y ∧ y ≤ x + k + j)) ∨
        y = x - k - 1 - 3 * j := by
  have ht : ∀ i, i < j → k + 2 * i + 1 < x - i → Visited k (x - i - (k + 2 * i + 1)) :=
    fun i hi h => by
      rw [show x - i - (k + 2 * i + 1) = x - k - 1 - 3 * i by omega]
      exact htest i hi (by omega)
  have e := zigzag_jump hx hj hfree ht (by omega)
    (by rw [show x - j - (k + 2 * j + 1) = x - k - 1 - 3 * j by omega]; exact hnew)
  rw [show x - j - (k + 2 * j + 1) = x - k - 1 - 3 * j by omega] at e
  obtain ⟨-, hv⟩ := zig_block hx hj hfree htest
  refine ⟨e, fun y => ?_⟩
  rw [visited_succ, hv, e]

/-! ## The machine -/

structure St where
  n : Nat
  x : Nat
  t : IT

/-- `s` faithfully represents the walk after `s.n` steps. -/
def Rep (s : St) : Prop :=
  1 ≤ s.n ∧ s.x = a s.n ∧ Sorted s.t.toList ∧ ∀ y, cover s.t.toList y ↔ Visited s.n y

/-- Fuel for the bounded loops; it is never the limiting factor in practice. -/
def bigFuel : Nat := 2 ^ 64

def single (s : St) : Option St :=
  if s.n + 1 < s.x ∧ s.t.mem (s.x - (s.n + 1)) = false then
    (s.t.insRange bigFuel (s.x - (s.n + 1)) (s.x - (s.n + 1))).map
      fun t => ⟨s.n + 1, s.x - (s.n + 1), t⟩
  else
    (s.t.insRange bigFuel (s.x + (s.n + 1)) (s.x + (s.n + 1))).map
      fun t => ⟨s.n + 1, s.x + (s.n + 1), t⟩

def full (s : St) (R : Nat) : Option St :=
  match s.t.insRange bigFuel (s.x - R) (s.x - 1) with
  | none => none
  | some t1 =>
    (t1.insRange bigFuel (s.x + s.n + 1) (s.x + s.n + R)).map fun t2 => ⟨s.n + 2 * R, s.x - R, t2⟩

def jump (s : St) (j : Nat) : Option St :=
  match s.t.insRange bigFuel (s.x - j) (s.x - 1) with
  | none => none
  | some t1 =>
    match t1.insRange bigFuel (s.x + s.n + 1) (s.x + s.n + j) with
    | none => none
    | some t2 =>
      (t2.insRange bigFuel (s.x - s.n - 1 - 3 * j) (s.x - s.n - 1 - 3 * j)).map
        fun t3 => ⟨s.n + 2 * j + 1, s.x - s.n - 1 - 3 * j, t3⟩

/-- One zigzag (capped so as not to pass step `N`), possibly ending in a jump. -/
def zig (N : Nat) (s : St) : Option St :=
  match s.t.firstFree bigFuel (s.x - s.n - 1) (min (s.t.freeBelow s.x) ((N - s.n) / 2)) 0 with
  | none => none
  | some (some j) =>
    if s.n + 2 * j + 1 ≤ N then jump s j else full s (min (s.t.freeBelow s.x) ((N - s.n) / 2))
  | some none => full s (min (s.t.freeBelow s.x) ((N - s.n) / 2))

def iter (N : Nat) (s : St) : Option St :=
  match zig N s with
  | none => none
  | some s1 => if s.n < s1.n then some s1 else single s1

def run : Nat → Nat → St → Option St
  | 0, _, _ => none
  | f + 1, N, s =>
    if N ≤ s.n then some s else
    match iter N s with
    | none => none
    | some s1 => run f N s1

/-- The state after one step: `a 1 = 1`, visited set `{0, 1}`. -/
def init : St := ⟨1, 1, .node .leaf 0 1 .leaf 1⟩

/-! ## Correctness -/

theorem cover_congr {L L' : List Iv} {n : Nat} {P : Nat → Prop}
    (h1 : ∀ y, cover L' y ↔ cover L y ∨ P y) (h2 : ∀ y, cover L y ↔ Visited n y) (m : Nat)
    (h3 : ∀ y, Visited m y ↔ Visited n y ∨ P y) : ∀ y, cover L' y ↔ Visited m y := by
  intro y; rw [h1, h2, h3]

theorem single_spec {s s' : St} (hs : Rep s) (h : single s = some s') :
    Rep s' ∧ s'.n = s.n + 1 := by
  obtain ⟨hn, hx, hsort, hcov⟩ := hs
  have hmem : ∀ y, s.t.mem y = true ↔ Visited s.n y := fun y => by
    rw [IT.mem_iff _ hsort, hcov]
  unfold single at h
  split at h
  · rename_i hc
    have hb : Back s.n := ⟨by rw [← hx]; exact hc.1, by
      rw [← hx, ← hmem]; simp [hc.2]⟩
    have e := a_succ_of_back hb
    cases ht : s.t.insRange bigFuel (s.x - (s.n + 1)) (s.x - (s.n + 1)) with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h; cases h
      obtain ⟨hs', hc'⟩ := IT.insRange_spec _ _ hsort _ _ _ ht
      refine ⟨⟨show 1 ≤ s.n + 1 by omega, by simp [e, hx], hs', ?_⟩, rfl⟩
      intro y
      rw [hc', hcov, visited_succ, e, ← hx]
      constructor <;> rintro (h | h) <;> first | exact Or.inl h | (right; omega)
  · rename_i hc
    have hb : ¬ Back s.n := by
      rintro ⟨h1, h2⟩
      apply hc
      refine ⟨by rw [hx]; exact h1, ?_⟩
      cases hm : s.t.mem (s.x - (s.n + 1)) with
      | false => rfl
      | true => exact absurd ((hmem _).1 hm) (by rw [hx]; exact h2)
    have e := a_succ_of_not_back hb
    cases ht : s.t.insRange bigFuel (s.x + (s.n + 1)) (s.x + (s.n + 1)) with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h; cases h
      obtain ⟨hs', hc'⟩ := IT.insRange_spec _ _ hsort _ _ _ ht
      refine ⟨⟨show 1 ≤ s.n + 1 by omega, by simp [e, hx], hs', ?_⟩, rfl⟩
      intro y
      rw [hc', hcov, visited_succ, e, ← hx]
      constructor <;> rintro (h | h) <;> first | exact Or.inl h | (right; omega)

theorem full_spec {s s' : St} {R : Nat} (hs : Rep s) (hR : R < s.x)
    (hfree : ∀ i, 1 ≤ i → i ≤ R → ¬ Visited s.n (s.x - i))
    (htest : ∀ j, j < R → 3 * j < s.x - s.n - 1 → Visited s.n (s.x - s.n - 1 - 3 * j))
    (h : full s R = some s') : Rep s' ∧ s'.n = s.n + 2 * R := by
  obtain ⟨hn, hx, hsort, hcov⟩ := hs
  obtain ⟨e, hv⟩ := zig_block hx.symm hR hfree htest
  unfold full at h
  split at h
  · cases h
  · rename_i t1 ht1
    cases ht2 : t1.insRange bigFuel (s.x + s.n + 1) (s.x + s.n + R) with
    | none => rw [ht2] at h; cases h
    | some t2 =>
      rw [ht2] at h; cases h
      obtain ⟨hs1, hc1⟩ := IT.insRange_spec _ _ hsort _ _ _ ht1
      obtain ⟨hs2, hc2⟩ := IT.insRange_spec _ _ hs1 _ _ _ ht2
      refine ⟨⟨show 1 ≤ s.n + 2 * R by omega, e.symm, hs2, fun y => ?_⟩, rfl⟩
      rw [hc2, hc1, hcov, hv]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem jump_spec {s s' : St} {j : Nat} (hs : Rep s) (hj : j < s.x)
    (hfree : ∀ i, 1 ≤ i → i ≤ j → ¬ Visited s.n (s.x - i))
    (htest : ∀ i, i < j → 3 * i < s.x - s.n - 1 → Visited s.n (s.x - s.n - 1 - 3 * i))
    (hpos : 3 * j < s.x - s.n - 1) (hnew : ¬ Visited s.n (s.x - s.n - 1 - 3 * j))
    (h : jump s j = some s') : Rep s' ∧ s'.n = s.n + 2 * j + 1 := by
  obtain ⟨hn, hx, hsort, hcov⟩ := hs
  obtain ⟨e, hv⟩ := jump_block hx.symm hj hfree htest hpos hnew
  unfold jump at h
  split at h
  · cases h
  · rename_i t1 ht1
    split at h
    · cases h
    · rename_i t2 ht2
      cases ht3 : t2.insRange bigFuel (s.x - s.n - 1 - 3 * j) (s.x - s.n - 1 - 3 * j) with
      | none => rw [ht3] at h; cases h
      | some t3 =>
        rw [ht3] at h; cases h
        obtain ⟨hs1, hc1⟩ := IT.insRange_spec _ _ hsort _ _ _ ht1
        obtain ⟨hs2, hc2⟩ := IT.insRange_spec _ _ hs1 _ _ _ ht2
        obtain ⟨hs3, hc3⟩ := IT.insRange_spec _ _ hs2 _ _ _ ht3
        refine ⟨⟨show 1 ≤ s.n + 2 * j + 1 by omega, e.symm, hs3, fun y => ?_⟩, rfl⟩
        rw [hc3, hc2, hc1, hcov, hv]
        constructor
        · rintro (((h | h) | h) | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr (by omega)
        · rintro ((h | h | h) | h)
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inl (Or.inl (Or.inr h))
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨by omega, by omega⟩

theorem zig_spec {N : Nat} {s s' : St} (hs : Rep s) (hN : s.n ≤ N) (h : zig N s = some s') :
    Rep s' ∧ s.n ≤ s'.n ∧ s'.n ≤ N := by
  have hs0 := hs
  obtain ⟨hn, hx, hsort, hcov⟩ := hs
  have hxpos : 0 < s.x := by rw [hx]; exact a_pos (by omega)
  obtain ⟨hfb1, hfb2⟩ := IT.freeBelow_spec s.t hsort s.x
  have hfree : ∀ R, R ≤ s.t.freeBelow s.x → ∀ i, 1 ≤ i → i ≤ R → ¬ Visited s.n (s.x - i) :=
    fun R hR i h1 h2 hv => hfb2 i h1 (by omega) ((hcov _).2 hv)
  unfold zig at h
  split at h
  · cases h
  · rename_i j hff
    have hj := IT.firstFree_spec s.t hsort _ _ _ _ _ hff
    obtain ⟨-, hj1, hj2, hj3, hj4⟩ := hj
    split at h
    · obtain ⟨h1, h2⟩ := jump_spec hs0 (by omega) (hfree j (by omega))
        (fun i hi _ => (hcov _).1 (hj4 i (by omega) hi)) hj2 (fun hv => hj3 ((hcov _).2 hv)) h
      exact ⟨h1, by omega, by omega⟩
    · -- the jump would pass step `N`, so it is exactly at round `R`
      obtain ⟨h1, h2⟩ := full_spec hs0 (by omega) (hfree _ (Nat.min_le_left _ _))
        (fun i hi _ => (hcov _).1 (hj4 i (by omega) (by omega))) h
      exact ⟨h1, by omega, by omega⟩
  · rename_i hff
    have hj := IT.firstFree_spec s.t hsort _ _ _ _ _ hff
    obtain ⟨h1, h2⟩ := full_spec hs0 (by omega) (hfree _ (Nat.min_le_left _ _))
      (fun i hi h3 => (hcov _).1 (hj i (by omega) (by omega) h3)) h
    exact ⟨h1, by omega, by omega⟩

theorem iter_spec {N : Nat} {s s' : St} (hs : Rep s) (hN : s.n < N) (h : iter N s = some s') :
    Rep s' ∧ s.n < s'.n ∧ s'.n ≤ N := by
  unfold iter at h
  split at h
  · cases h
  · rename_i s1 h1
    obtain ⟨r1, l1, u1⟩ := zig_spec hs (by omega) h1
    split at h
    · cases h; exact ⟨r1, by omega, u1⟩
    · obtain ⟨r2, e2⟩ := single_spec r1 h
      exact ⟨r2, by omega, by omega⟩

theorem run_spec (f N : Nat) : ∀ s s', Rep s → s.n ≤ N → run f N s = some s' →
    Rep s' ∧ s'.n = N := by
  induction f with
  | zero => intro s s' _ _ h; cases h
  | succ f ih =>
    intro s s' hs hN h
    simp only [run] at h
    split at h
    · cases h; exact ⟨hs, by omega⟩
    · split at h
      · cases h
      · rename_i s1 h1
        obtain ⟨r1, l1, u1⟩ := iter_spec hs (by omega) h1
        exact ih s1 s' r1 u1 h

theorem init_rep : Rep init := by
  refine ⟨Nat.le_refl _, rfl, ⟨by simp [init, IT.toList], by simp [init, IT.toList]⟩, fun y => ?_⟩
  simp only [init, IT.toList, cover, List.nil_append, List.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨-, h⟩
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, Nat.le_refl _, rfl⟩
  · rintro ⟨i, hi, hai⟩
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact ⟨Nat.zero_le _, by rw [← hai]; decide⟩
    · exact ⟨Nat.zero_le _, by rw [← hai]; decide⟩

/-- Run to step `N` and report: is every `m < M` visited, and is `miss` unvisited? -/
def check (N M miss : Nat) : Bool :=
  match run bigFuel N init with
  | some s => s.t.covRange bigFuel 0 (M - 1) && !(s.t.mem miss)
  | none => false

theorem check_sound {N M miss : Nat} (hN : 1 ≤ N) (hM : 1 ≤ M) (h : check N M miss = true) :
    (∀ m, m < M → Visited N m) ∧ ¬ Visited N miss := by
  unfold check at h
  split at h
  · rename_i s hr
    obtain ⟨⟨_, _, hsort, hcov⟩, hn⟩ := run_spec _ _ _ _ init_rep hN hr
    rw [Bool.and_eq_true] at h
    subst hn
    refine ⟨fun m hm => (hcov m).1 (IT.covRange_spec _ hsort _ _ _ h.1 m (by omega) (by omega)),
      fun hv => ?_⟩
    have := (IT.mem_iff _ hsort miss).2 ((hcov miss).2 hv)
    simp [this] at h
  · cases h

/-- Run to step `N₁` and check that every interval of `cov` is visited; continue to step `N₂`
and check that every number in `miss` is still unvisited. -/
def check2 (N₁ N₂ : Nat) (cov : List (Nat × Nat)) (miss : List Nat) : Bool :=
  match run bigFuel N₁ init with
  | none => false
  | some s₁ =>
    cov.all (fun p => s₁.t.covRange bigFuel p.1 p.2) &&
      match run bigFuel N₂ s₁ with
      | none => false
      | some s₂ => miss.all (fun m => !(s₂.t.mem m))

theorem check2_sound {N₁ N₂ : Nat} {cov : List (Nat × Nat)} {miss : List Nat} (h1 : 1 ≤ N₁)
    (h12 : N₁ ≤ N₂) (h : check2 N₁ N₂ cov miss = true) :
    (∀ p ∈ cov, ∀ y, p.1 ≤ y → y ≤ p.2 → Visited N₁ y) ∧ ∀ m ∈ miss, ¬ Visited N₂ m := by
  unfold check2 at h
  split at h
  · cases h
  · rename_i s₁ hr₁
    obtain ⟨⟨hn₁, hx₁, hsort₁, hcov₁⟩, he₁⟩ := run_spec _ _ _ _ init_rep h1 hr₁
    rw [Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun p hp y hy1 hy2 => ?_, ?_⟩
    · rw [← he₁]
      exact (hcov₁ y).1 (IT.covRange_spec _ hsort₁ _ _ _ (by simpa using h.1 p hp) y hy1 hy2)
    · have h2 := h.2
      split at h2
      · cases h2
      · rename_i s₂ hr₂
        obtain ⟨⟨-, -, hsort₂, hcov₂⟩, he₂⟩ := run_spec _ _ _ _ ⟨hn₁, hx₁, hsort₁, hcov₁⟩
          (by omega) hr₂
        rw [List.all_eq_true] at h2
        intro m hm hv
        have := (IT.mem_iff _ hsort₂ m).2 ((hcov₂ m).2 (he₂ ▸ hv))
        have := h2 m hm
        simp_all

end Recaman
