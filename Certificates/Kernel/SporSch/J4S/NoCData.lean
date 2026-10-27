
module

public import CFSG.Sporadic.Schreier.J4SNoCompData

public section

namespace CertificateChecks.KernelSporSch.J4NoC

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp

@[expose] def repPairs : Array Pair := Array.ofFn fun l : Fin 7 => repPair l.val

@[expose] def conjFlat : Array Pair :=
  (Array.range 77).map fun k => conjPair (k / 11) ⟨k % 11, Nat.mod_lt _ (by decide)⟩

@[expose] def pk (X : Array Nat) : Nat :=
  (List.range X.size).foldl (fun acc i => acc ||| (X[i]! <<< (128 * i))) 0

@[expose] def cB : Nat := (List.range 112).foldl (fun acc r => acc ||| (1 <<< (128 * r))) 0

@[expose] def mulPk (A B : Nat) : Nat :=
  (List.range 112).foldl (fun acc k =>
    acc ^^^ ((((A >>> k) &&& cB) * (2 ^ 112 - 1)) &&&
      (((B >>> (128 * k)) &&& (2 ^ 112 - 1)) * cB))) 0

@[expose] def firstRow (D : Nat) : Nat :=
  ((List.range 112).find? fun r => (D >>> (128 * r)) &&& (2 ^ 112 - 1) != 0).getD 0

@[expose] def wit (Gp : Array Nat) (Ea l a : Nat) : Nat :=
  if l = 0 ∨ a = 0 ∨ (dSets[l]!).contains a then 0 else
    ((List.range 11).findSome? fun j =>
      let Y := Gp[11 * l + j]!
      let D := mulPk Ea Y ^^^ mulPk Y Ea
      if D = 0 then none else some (1 + 112 * j + firstRow D)).getD 0

@[expose] def outW : Array (Array Nat) :=
  let Up := (Array.range 11).map fun j => pk (unMats[j]!)
  let Gp := conjFlat.map fun P => pk P.1
  let I := pk (Array.ofFn fun i : Fin 112 => 1 <<< i.val)
  let E := (Array.range 2048).map fun a =>
    (List.range 11).foldl (fun acc j => if a.testBit j then mulPk acc Up[j]! else acc) I
  Array.ofFn fun l : Fin 7 => Array.ofFn fun a : Fin 2048 => wit Gp E[a.val]! l.val a.val

end CertificateChecks.KernelSporSch.J4NoC

end
