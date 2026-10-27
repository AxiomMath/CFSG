module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval

meta def ixAt5 (s k : Nat) : Nat := (s >>> (5 * k)) % 32

meta def ixAmat (CP s a : Nat) : Nat :=
  (List.range 9).foldl
    (fun acc j => if a.testBit j then acc ^^^ ((CP >>> (9 * ixAt5 s j)) % 512) else acc) 0

meta def ixCommM (s t : Nat) : Bool :=
  (List.range 21).all fun k => ixAt5 s (ixAt5 t k) == ixAt5 t (ixAt5 s k)

public meta def ixStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.list R) := args[0]? | throw "ixStep: expected the list R"
  let some (Val.nat CP) := args[1]? | throw "ixStep: expected CP"
  let mut I : Array Nat := #[]
  for r in R do
    let Val.list xs := r | throw "ixStep: R entry"
    for x in xs do
      let Val.nat v := x | throw "ixStep: involution"
      I := I.push v
  let F := I.map fun s => (List.range 512).foldl
    (fun acc a => if ixAmat CP s a == a then acc ||| (1 <<< a) else acc) 0
  let C := I.map fun s => (List.range I.size).foldl
    (fun acc j => if ixCommM s I[j]! then acc ||| (1 <<< j) else acc) 0
  let D := (List.range I.size).toArray.map fun i => I[i]! + (F[i]! <<< 105) + (C[i]! <<< 617)
  return #[(`D, Val.list (D.map Val.nat))]

end CertificateChecks.KernelSmithEK
