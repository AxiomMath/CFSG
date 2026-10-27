module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.Co1B.GenTri2045
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Kernel.Co1B.GenTri2045

namespace CertificateChecks.KernelLC.Co1Cen2B

open CFSG.KC.Eval CFSG.KS.GenTri CFSG.KS.RawGen

public meta def rowsP (X : Nat) : Array Nat :=
  Array.ofFn (n := 24) fun i => (X >>> (24 * i.val)) &&& (2 ^ 24 - 1)

public meta def natArg (v : Val) : Except String Nat :=
  match v with
  | .nat n => .ok n
  | _ => .error "expected a natural number"

public meta def triStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 8 then throw "triStep: expected 8 arguments"
  let ns ← args.mapM natArg
  let PT := ns[0]!
  let R := fun (i : Nat) => rowsP ns[i]!
  let field := fun (i : Nat) => (PT >>> (24 * i)) &&& (2 ^ 24 - 1)
  let n := 1365
  let vec := fun (i : Nat) =>
    let u := field (2 * (i / 3))
    let v := field (2 * (i / 3) + 1)
    if i % 3 == 0 then u else if i % 3 == 1 then v else u ^^^ v
  let idx : Std.HashMap Nat Nat := (List.range 4095).foldl (fun m i => m.insert (vec i) (i / 3)) {}
  if idx.size != 4095 then throw "triStep: the triple vectors are not distinct"
  let perm := fun (M : Array Nat) => Id.run do
    let mut out : Array Nat := #[]
    for k in [0:n] do
      out := out.push (idx.getD (actR M (vec (3 * k))) n)
    return out
  let check := fun (M : Array Nat) (p : Array Nat) => (List.range n).all fun k =>
    p[k]! < n && idx.getD (actR M (vec (3 * k + 1))) n == p[k]! &&
      idx.getD (actR M (vec (3 * k + 2))) n == p[k]!
  let XY := mulR (R 1) (R 2)
  let mut E := XY
  for _ in [0:12] do
    E := mulR E XY
  let Z := mulR (mulR (R 3) (R 4)) (mulR (R 5) (R 6))
  let C := R 7
  let pE := perm E
  let pZ := perm Z
  let pC := perm C
  if !(check E pE && pE == Array.range n) then throw "triStep: e₂ does not act trivially"
  if !check Z pZ then throw "triStep: z does not map triples onto triples"
  if !check C pC then throw "triStep: C does not map triples onto triples"
  let pZ2 := comp n pZ pZ
  if pZ2 == Array.range n then throw "triStep: φ(z)² = 1"
  let sw := swaps pC
  if (sw.size / 2) % 2 != 1 then throw "triStep: φ(C) is even"
  return #[(`E, .nat (packM E)), (`Z, .nat (packM Z)), (`T1, .nat (packM (trR E))),
    (`T2, .nat (packM (trR Z))), (`T3, .nat (packM (trR C))), (`PZ, .nat (pack 11 pZ)), (`PZ2, .nat (pack 11 pZ2)), (`PC, .nat (pack 11 pC)),
    (`PCI, .nat (pack 11 (inv n pC))), (`SW, .nat (pack 11 sw)), (`SK, .nat (sw.size / 2))]

end CertificateChecks.KernelLC.Co1Cen2B
