/-!
# Interval sets, verified

A finite set of naturals stored as disjoint intervals `[lo, hi]` in a balanced search tree.
`IT.findLE` (last interval starting at or below `y`) is the one query everything else is
built on. Balance only matters for speed; correctness is proved through the in-order list
`toList`, which must be `Sorted` (each interval ends before the next one starts).
-/

namespace Recaman

abbrev Iv := Nat × Nat

/-- `y` lies in some interval of `L`. -/
def cover (L : List Iv) (y : Nat) : Prop := ∃ p ∈ L, p.1 ≤ y ∧ y ≤ p.2

/-- Intervals are nonempty and in increasing order with gaps (or adjacency) between them. -/
def Sorted (L : List Iv) : Prop := L.Pairwise (fun p q => p.2 < q.1) ∧ ∀ p ∈ L, p.1 ≤ p.2

theorem Sorted.cons_iff {p : Iv} {L : List Iv} :
    Sorted (p :: L) ↔ (∀ q ∈ L, p.2 < q.1) ∧ p.1 ≤ p.2 ∧ Sorted L := by
  unfold Sorted
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h3, h2, h4⟩
  · rintro ⟨h1, h3, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem Sorted.append_iff {L₁ L₂ : List Iv} :
    Sorted (L₁ ++ L₂) ↔ Sorted L₁ ∧ Sorted L₂ ∧ ∀ p ∈ L₁, ∀ q ∈ L₂, p.2 < q.1 := by
  unfold Sorted
  simp only [List.pairwise_append, List.mem_append]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨⟨h1, fun p hp => h4 p (Or.inl hp)⟩, ⟨h2, fun p hp => h4 p (Or.inr hp)⟩, h3⟩
  · rintro ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, h3⟩
    exact ⟨⟨h1, h2, h3⟩, fun p hp => hp.elim (h1' p) (h2' p)⟩

/-! ## The last interval starting at or below `y` -/

def lastLE : List Iv → Nat → Option Iv
  | [], _ => none
  | p :: L, y => (lastLE L y).or (if p.1 ≤ y then some p else none)

theorem lastLE_append (L₁ L₂ : List Iv) (y : Nat) :
    lastLE (L₁ ++ L₂) y = (lastLE L₂ y).or (lastLE L₁ y) := by
  induction L₁ with
  | nil => show lastLE L₂ y = (lastLE L₂ y).or none; cases lastLE L₂ y <;> rfl
  | cons p L ih =>
    show (lastLE (L ++ L₂) y).or _ = (lastLE L₂ y).or ((lastLE L y).or _)
    rw [ih, Option.or_assoc]

theorem lastLE_some {L : List Iv} {y : Nat} {p : Iv} (h : lastLE L y = some p) :
    p ∈ L ∧ p.1 ≤ y := by
  induction L with
  | nil => cases h
  | cons q L ih =>
    simp only [lastLE] at h
    cases hl : lastLE L y with
    | some r =>
      rw [hl] at h; cases h
      exact ⟨List.mem_cons_of_mem _ (ih hl).1, (ih hl).2⟩
    | none =>
      rw [hl] at h
      by_cases hq : q.1 ≤ y
      · simp [hq] at h; subst h; exact ⟨List.mem_cons_self, hq⟩
      · simp [hq] at h

theorem lastLE_none {L : List Iv} {y : Nat} (h : lastLE L y = none) : ∀ q ∈ L, y < q.1 := by
  induction L with
  | nil => intro q hq; cases hq
  | cons p L ih =>
    simp only [lastLE] at h
    cases hl : lastLE L y with
    | some r => rw [hl] at h; cases h
    | none =>
      rw [hl] at h
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · by_cases hp : q.1 ≤ y
        · simp [hp] at h
        · omega
      · exact ih hl q hq

theorem lastLE_eq_none {L : List Iv} {y : Nat} (h : ∀ q ∈ L, y < q.1) : lastLE L y = none := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [lastLE]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have := h p List.mem_cons_self
    simp; omega

/-- In a sorted list, the interval found reaches at least as far as any interval starting
at or below `y`. -/
theorem lastLE_max {L : List Iv} (hs : Sorted L) {y : Nat} {p : Iv} (h : lastLE L y = some p) :
    ∀ q ∈ L, q.1 ≤ y → q.2 ≤ p.2 := by
  induction L with
  | nil => intro q hq; cases hq
  | cons r L ih =>
    obtain ⟨hr1, hr2, hs'⟩ := Sorted.cons_iff.1 hs
    simp only [lastLE] at h
    cases hl : lastLE L y with
    | some p' =>
      rw [hl] at h; simp only [Option.some_or, Option.some.injEq] at h; subst h
      intro q hq hqy
      rcases List.mem_cons.1 hq with rfl | hq
      · have := hr1 p' (lastLE_some hl).1
        have := hs'.2 p' (lastLE_some hl).1
        omega
      · exact ih hs' hl q hq hqy
    | none =>
      rw [hl] at h
      by_cases hry : r.1 ≤ y
      · simp [hry] at h; subst h
        intro q hq hqy
        rcases List.mem_cons.1 hq with rfl | hq
        · exact Nat.le_refl _
        · have := lastLE_none hl q hq; omega
      · simp [hry] at h

theorem cover_iff {L : List Iv} (hs : Sorted L) (y : Nat) :
    cover L y ↔ ∃ p, lastLE L y = some p ∧ y ≤ p.2 := by
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    cases hl : lastLE L y with
    | none => have := lastLE_none hl q hq; omega
    | some p => exact ⟨p, rfl, by have := lastLE_max hs hl q hq h1; omega⟩
  · rintro ⟨p, hp, hy⟩
    exact ⟨p, (lastLE_some hp).1, (lastLE_some hp).2, hy⟩

theorem uncovered_above {L : List Iv} (hs : Sorted L) {y : Nat} {p : Iv}
    (h : lastLE L y = some p) {z : Nat} (h1 : p.2 < z) (h2 : z ≤ y) : ¬ cover L z := by
  rintro ⟨q, hq, hq1, hq2⟩
  have := lastLE_max hs h q hq (by omega)
  omega

theorem uncovered_none {L : List Iv} {y : Nat} (h : lastLE L y = none) {z : Nat} (hz : z ≤ y) :
    ¬ cover L z := by
  rintro ⟨q, hq, hq1, _⟩
  have := lastLE_none h q hq
  omega

/-! ## Sorted insertion of an interval disjoint from the others -/

def insL : List Iv → Iv → List Iv
  | [], I => [I]
  | p :: L, I => if I.1 < p.1 then I :: p :: L else p :: insL L I

theorem mem_insL {L : List Iv} {I q : Iv} : q ∈ insL L I ↔ q = I ∨ q ∈ L := by
  induction L with
  | nil => simp [insL]
  | cons p L ih =>
    simp only [insL]
    split
    · simp
    · simp only [List.mem_cons, ih, or_left_comm]

theorem cover_insL (L : List Iv) (I : Iv) (y : Nat) :
    cover (insL L I) y ↔ cover L y ∨ (I.1 ≤ y ∧ y ≤ I.2) := by
  unfold cover
  constructor
  · rintro ⟨q, hq, h⟩
    rcases mem_insL.1 hq with rfl | hq
    · exact Or.inr h
    · exact Or.inl ⟨q, hq, h⟩
  · rintro (⟨q, hq, h⟩ | h)
    · exact ⟨q, mem_insL.2 (Or.inr hq), h⟩
    · exact ⟨I, mem_insL.2 (Or.inl rfl), h⟩

theorem sorted_insL {L : List Iv} (hs : Sorted L) {I : Iv} (hI : I.1 ≤ I.2)
    (hsep : ∀ q ∈ L, q.2 < I.1 ∨ I.2 < q.1) : Sorted (insL L I) := by
  induction L with
  | nil => exact Sorted.cons_iff.2 ⟨(fun q hq => by cases hq), hI, ⟨List.Pairwise.nil, by simp⟩⟩
  | cons p L ih =>
    obtain ⟨hp1, hp2, hs'⟩ := Sorted.cons_iff.1 hs
    simp only [insL]
    split
    · rename_i hlt
      refine Sorted.cons_iff.2 ⟨?_, hI, hs⟩
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · rcases hsep q List.mem_cons_self with h | h <;> omega
      · have := hp1 q hq
        have := hs'.2 q hq
        rcases hsep q (List.mem_cons_of_mem _ hq) with h | h <;> omega
    · rename_i hge
      refine Sorted.cons_iff.2 ⟨?_, hp2, ih hs' (fun q hq => hsep q (List.mem_cons_of_mem _ hq))⟩
      intro q hq
      rcases mem_insL.1 hq with rfl | hq
      · rcases hsep p List.mem_cons_self with h | h <;> omega
      · exact hp1 q hq

/-- An interval with no covered point is separated from every interval of the list. -/
theorem sep_of_free {L : List Iv} (hs : Sorted L) {I : Iv} (hI : I.1 ≤ I.2)
    (h : ∀ z, I.1 ≤ z → z ≤ I.2 → ¬ cover L z) : ∀ q ∈ L, q.2 < I.1 ∨ I.2 < q.1 := by
  intro q hq
  have := hs.2 q hq
  apply Classical.byContradiction
  intro hn
  by_cases hq1 : I.1 ≤ q.1
  · exact h q.1 hq1 (by omega) ⟨q, hq, Nat.le_refl _, by omega⟩
  · exact h I.1 (Nat.le_refl _) (by omega) ⟨q, hq, by omega, by omega⟩

/-! ## The tree -/

inductive IT where
  | leaf : IT
  | node : IT → Nat → Nat → IT → Nat → IT

namespace IT

def toList : IT → List Iv
  | leaf => []
  | node l lo hi r _ => l.toList ++ (lo, hi) :: r.toList

def height : IT → Nat
  | leaf => 0
  | node _ _ _ _ h => h

def mk (l : IT) (lo hi : Nat) (r : IT) : IT := node l lo hi r (max l.height r.height + 1)

/-- AVL rebalancing (only for speed: it never changes the in-order list). -/
def bal (l : IT) (lo hi : Nat) (r : IT) : IT :=
  if r.height + 1 < l.height then
    match l with
    | node ll llo lhi lr _ =>
      if lr.height ≤ ll.height then mk ll llo lhi (mk lr lo hi r)
      else match lr with
        | node lrl lrlo lrhi lrr _ => mk (mk ll llo lhi lrl) lrlo lrhi (mk lrr lo hi r)
        | leaf => mk l lo hi r
    | leaf => mk l lo hi r
  else if l.height + 1 < r.height then
    match r with
    | node rl rlo rhi rr _ =>
      if rl.height ≤ rr.height then mk (mk l lo hi rl) rlo rhi rr
      else match rl with
        | node rll rllo rlhi rlr _ => mk (mk l lo hi rll) rllo rlhi (mk rlr rlo rhi rr)
        | leaf => mk l lo hi r
    | leaf => mk l lo hi r
  else mk l lo hi r

theorem toList_mk (l : IT) (lo hi : Nat) (r : IT) :
    (mk l lo hi r).toList = l.toList ++ (lo, hi) :: r.toList := rfl

theorem toList_bal (l : IT) (lo hi : Nat) (r : IT) :
    (bal l lo hi r).toList = l.toList ++ (lo, hi) :: r.toList := by
  unfold bal
  repeat' split
  all_goals simp_all [toList, toList_mk, List.append_assoc]

def ins : IT → Nat → Nat → IT
  | leaf, lo, hi => mk leaf lo hi leaf
  | node l plo phi r _, lo, hi =>
    if lo < plo then bal (l.ins lo hi) plo phi r else bal l plo phi (r.ins lo hi)

theorem insL_append_of_lt {I p : Iv} (h : I.1 < p.1) (L₁ L₂ : List Iv) :
    insL (L₁ ++ p :: L₂) I = insL L₁ I ++ p :: L₂ := by
  induction L₁ with
  | nil => simp [insL, h]
  | cons q L ih =>
    simp only [List.cons_append, insL]
    split
    · rfl
    · rw [ih]; rfl

theorem insL_append_of_ge {I : Iv} (L₁ L₂ : List Iv) (h : ∀ q ∈ L₁, ¬ I.1 < q.1) :
    insL (L₁ ++ L₂) I = L₁ ++ insL L₂ I := by
  induction L₁ with
  | nil => rfl
  | cons q L ih =>
    simp only [List.cons_append, insL]
    simp only [h q List.mem_cons_self, ite_false]
    rw [ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]

theorem toList_ins (t : IT) (hs : Sorted t.toList) (lo hi : Nat) :
    (t.ins lo hi).toList = insL t.toList (lo, hi) := by
  induction t with
  | leaf => rfl
  | node l plo phi r _ ihl ihr =>
    simp only [toList] at hs
    obtain ⟨hl, hpr, hlr⟩ := Sorted.append_iff.1 hs
    obtain ⟨hp1, hp2, hr⟩ := Sorted.cons_iff.1 hpr
    simp only [ins, toList]
    split
    · rename_i hlt
      rw [toList_bal, ihl hl, insL_append_of_lt (p := (plo, phi)) hlt]
    · rename_i hge
      rw [toList_bal, ihr hr, insL_append_of_ge]
      · simp only [insL, hge, ite_false]
      · intro q hq
        have := hlr q hq (plo, phi) List.mem_cons_self
        have := hl.2 q hq
        simp only at this hge ⊢
        omega

def findLE : IT → Nat → Option Iv
  | leaf, _ => none
  | node l lo hi r _, y => if y < lo then l.findLE y else (r.findLE y).or (some (lo, hi))

theorem findLE_eq (t : IT) (hs : Sorted t.toList) (y : Nat) : t.findLE y = lastLE t.toList y := by
  induction t with
  | leaf => rfl
  | node l lo hi r _ ihl ihr =>
    simp only [toList] at hs
    obtain ⟨hl, hpr, hlr⟩ := Sorted.append_iff.1 hs
    obtain ⟨hp1, hp2, hr⟩ := Sorted.cons_iff.1 hpr
    simp only [findLE, toList, lastLE_append, lastLE]
    split
    · rename_i hlt
      rw [ihl hl, lastLE_eq_none (L := r.toList) (fun q hq => by have := hp1 q hq; simp at hp2 ⊢; omega)]
      have : ¬ lo ≤ y := by omega
      simp [this]
    · rename_i hge
      rw [ihr hr]
      have : lo ≤ y := by omega
      simp only [this, ite_true]
      cases lastLE r.toList y <;> rfl

/-- Is `y` in the set? -/
def mem (t : IT) (y : Nat) : Bool :=
  match t.findLE y with
  | some p => decide (y ≤ p.2)
  | none => false

theorem mem_iff (t : IT) (hs : Sorted t.toList) (y : Nat) : t.mem y = true ↔ cover t.toList y := by
  rw [cover_iff hs, ← findLE_eq t hs]
  unfold mem
  cases t.findLE y with
  | none => simp
  | some p => simp

/-- Insert the interval `[lo, hi]` (union), inserting only its uncovered pieces. -/
def insRange : Nat → IT → Nat → Nat → Option IT
  | 0, _, _, _ => none
  | fuel + 1, t, lo, hi =>
    if hi < lo then some t else
    match t.findLE hi with
    | none => some (t.ins lo hi)
    | some (l', h') =>
      if h' < lo then some (t.ins lo hi) else
      if l' ≤ lo then some (if h' < hi then t.ins (h' + 1) hi else t)
      else insRange fuel (if h' < hi then t.ins (h' + 1) hi else t) lo (l' - 1)

theorem ins_spec {t : IT} (hs : Sorted t.toList) {lo hi : Nat} (hlh : lo ≤ hi)
    (hfree : ∀ z, lo ≤ z → z ≤ hi → ¬ cover t.toList z) :
    Sorted (t.ins lo hi).toList ∧
      ∀ y, cover (t.ins lo hi).toList y ↔ cover t.toList y ∨ (lo ≤ y ∧ y ≤ hi) := by
  rw [toList_ins t hs]
  exact ⟨sorted_insL hs hlh (sep_of_free hs (I := (lo, hi)) hlh hfree), fun y => cover_insL _ _ y⟩

theorem insRange_spec (fuel : Nat) (t : IT) (hs : Sorted t.toList) (lo hi : Nat) (t' : IT)
    (h : insRange fuel t lo hi = some t') :
    Sorted t'.toList ∧ ∀ y, cover t'.toList y ↔ cover t.toList y ∨ (lo ≤ y ∧ y ≤ hi) := by
  induction fuel generalizing t hi with
  | zero => cases h
  | succ fuel ih =>
    simp only [insRange] at h
    split at h
    · cases h; exact ⟨hs, fun y => ⟨Or.inl, fun h' => h'.elim id (fun h'' => by omega)⟩⟩
    rename_i hlh
    have hfl := findLE_eq t hs hi
    split at h
    · rename_i hn
      cases h
      exact ins_spec hs (by omega) (fun z _ hz => uncovered_none (hfl ▸ hn) hz)
    · rename_i l' h' hp
      rw [hfl] at hp
      have hpm := lastLE_some hp
      have hpc := hs.2 _ hpm.1
      simp only at hpc hpm
      -- the piece above `h'` is free
      have hup : Sorted (if h' < hi then t.ins (h' + 1) hi else t).toList ∧
          ∀ y, cover (if h' < hi then t.ins (h' + 1) hi else t).toList y ↔
            cover t.toList y ∨ (h' + 1 ≤ y ∧ y ≤ hi) := by
        split
        · exact ins_spec hs (by omega) (fun z hz1 hz2 => uncovered_above hs hp (by simp; omega) hz2)
        · exact ⟨hs, fun y => ⟨Or.inl, fun h'' => h''.elim id (fun h3 => by omega)⟩⟩
      have hcov : ∀ y, l' ≤ y → y ≤ h' → cover t.toList y := fun y h1 h2 =>
        ⟨(l', h'), hpm.1, h1, h2⟩
      split at h
      · cases h
        exact ins_spec hs (by omega) (fun z hz1 hz2 => uncovered_above hs hp (by simp; omega) hz2)
      split at h
      · cases h
        refine ⟨hup.1, fun y => ?_⟩
        rw [hup.2 y]
        constructor
        · rintro (h1 | h1)
          · exact Or.inl h1
          · exact Or.inr ⟨by omega, h1.2⟩
        · rintro (h1 | h1)
          · exact Or.inl h1
          · by_cases hy : y ≤ h'
            · exact Or.inl (hcov y (by omega) hy)
            · exact Or.inr ⟨by omega, h1.2⟩
      · obtain ⟨hs'', hc''⟩ := ih _ hup.1 _ h
        refine ⟨hs'', fun y => ?_⟩
        rw [hc'' y, hup.2 y]
        constructor
        · rintro ((h1 | h1) | h1)
          · exact Or.inl h1
          · exact Or.inr ⟨by omega, h1.2⟩
          · exact Or.inr ⟨h1.1, by omega⟩
        · rintro (h1 | h1)
          · exact Or.inl (Or.inl h1)
          · by_cases hy1 : y < l'
            · exact Or.inr ⟨h1.1, by omega⟩
            · by_cases hy2 : y ≤ h'
              · exact Or.inl (Or.inl (hcov y (by omega) hy2))
              · exact Or.inl (Or.inr ⟨by omega, h1.2⟩)

/-- Length of the uncovered run just below `x` (at most `x - 1`). -/
def freeBelow (t : IT) (x : Nat) : Nat :=
  match t.findLE (x - 1) with
  | none => x - 1
  | some p => if p.2 < x - 1 then x - 1 - p.2 else 0

theorem freeBelow_spec (t : IT) (hs : Sorted t.toList) (x : Nat) :
    t.freeBelow x ≤ x - 1 ∧ ∀ i, 1 ≤ i → i ≤ t.freeBelow x → ¬ cover t.toList (x - i) := by
  have hfl := findLE_eq t hs (x - 1)
  unfold freeBelow
  cases hf : t.findLE (x - 1) with
  | none =>
    rw [hf] at hfl
    exact ⟨Nat.le_refl _, fun i _ _ => uncovered_none hfl.symm (by omega)⟩
  | some p =>
    rw [hf] at hfl
    simp only
    split
    · exact ⟨by omega, fun i h1 h2 => uncovered_above hs hfl.symm (by omega) (by omega)⟩
    · exact ⟨by omega, fun i h1 h2 => by omega⟩

/-- The first `j ≥ j₀` with `j ≤ jmax` and `3j < P` such that `P - 3j` is uncovered
(`some (some j)`), or `some none` if there is none; `none` means the fuel ran out. -/
def firstFree : Nat → IT → Nat → Nat → Nat → Option (Option Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, t, P, jmax, j =>
    if jmax < j ∨ P ≤ 3 * j then some none else
    match t.findLE (P - 3 * j) with
    | none => some (some j)
    | some p => if p.2 < P - 3 * j then some (some j) else firstFree fuel t P jmax ((P - p.1) / 3 + 1)

theorem firstFree_spec (t : IT) (hs : Sorted t.toList) (P jmax : Nat) :
    ∀ fuel j₀ r, t.firstFree fuel P jmax j₀ = some r →
      match r with
      | some j => j₀ ≤ j ∧ j ≤ jmax ∧ 3 * j < P ∧ ¬ cover t.toList (P - 3 * j) ∧
          ∀ i, j₀ ≤ i → i < j → cover t.toList (P - 3 * i)
      | none => ∀ i, j₀ ≤ i → i ≤ jmax → 3 * i < P → cover t.toList (P - 3 * i) := by
  intro fuel
  induction fuel with
  | zero => intro j₀ r h; cases h
  | succ fuel ih =>
    intro j₀ r h
    simp only [firstFree] at h
    split at h
    · cases h; intro i h1 h2 h3; omega
    rename_i hstop
    have hfl := findLE_eq t hs (P - 3 * j₀)
    split at h
    · rename_i hn
      cases h
      exact ⟨Nat.le_refl _, by omega, by omega, uncovered_none (hfl ▸ hn) (Nat.le_refl _),
        fun i h1 h2 => by omega⟩
    · rename_i p hp
      rw [hfl] at hp
      have hpm := lastLE_some hp
      split at h
      · cases h
        exact ⟨Nat.le_refl _, by omega, by omega,
          uncovered_above hs hp (by omega) (Nat.le_refl _), fun i h1 h2 => by omega⟩
      · rename_i hcov
        -- every candidate from `j₀` up to the next start is covered by `p`
        have hp' : ∀ i, j₀ ≤ i → i < (P - p.1) / 3 + 1 → 3 * i < P → cover t.toList (P - 3 * i) :=
          fun i h1 h2 h3 => ⟨p, hpm.1, by omega, by omega⟩
        have hnext := ih _ r h
        cases r with
        | some j =>
          obtain ⟨h1, h2, h3, h4, h5⟩ := hnext
          refine ⟨by omega, h2, h3, h4, fun i hi1 hi2 => ?_⟩
          by_cases hi : i < (P - p.1) / 3 + 1
          · exact hp' i hi1 hi (by omega)
          · exact h5 i (by omega) hi2
        | none =>
          intro i hi1 hi2 hi3
          by_cases hi : i < (P - p.1) / 3 + 1
          · exact hp' i hi1 hi hi3
          · exact hnext i (by omega) hi2 hi3

/-- Is every number in `[lo, hi]` covered? -/
def covRange : Nat → IT → Nat → Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, t, lo, hi =>
    if hi < lo then true else
    match t.findLE hi with
    | none => false
    | some p => if hi ≤ p.2 then (if p.1 ≤ lo then true else covRange fuel t lo (p.1 - 1)) else false

theorem covRange_spec (t : IT) (hs : Sorted t.toList) :
    ∀ fuel lo hi, t.covRange fuel lo hi = true → ∀ y, lo ≤ y → y ≤ hi → cover t.toList y := by
  intro fuel
  induction fuel with
  | zero => intro lo hi h; cases h
  | succ fuel ih =>
    intro lo hi h y h1 h2
    simp only [covRange] at h
    split at h
    · omega
    have hfl := findLE_eq t hs hi
    split at h
    · cases h
    · rename_i p hp
      rw [hfl] at hp
      have hpm := lastLE_some hp
      split at h
      · split at h
        · exact ⟨p, hpm.1, by omega, by omega⟩
        · by_cases hy : y < p.1
          · exact ih lo (p.1 - 1) h y h1 (by omega)
          · exact ⟨p, hpm.1, by omega, by omega⟩
      · cases h

end IT

end Recaman
