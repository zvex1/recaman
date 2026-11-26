import Recaman.Fast
open Recaman

/-- Smallest uncovered number (reporting only; not used in proofs). -/
partial def firstGap (t : IT) (y : Nat) : Nat :=
  match t.findLE y with
  | some p => if y ≤ p.2 then firstGap t (p.2 + 1) else y
  | none => y

def size : IT → Nat | .leaf => 0 | .node l _ _ r _ => size l + 1 + size r

def main (args : List String) : IO Unit := do
  let N := args.head!.toNat!
  match run bigFuel N init with
  | some s => IO.println s!"N={N} a(N)={s.x} smallest missing={firstGap s.t 0} intervals={size s.t}"
  | none => IO.println "fuel exhausted"
