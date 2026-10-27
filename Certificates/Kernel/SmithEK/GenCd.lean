module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LargeExtraspecial.S14SMKTransCheck

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th.Native

public meta def cdStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "cdStep: expected no arguments"
  let T := tvTabs
  let P := uaPts
  let W0 := P[0]!
  let W := wtArr
  let F := uaFlags P
  let PP := uaPtPlanes P
  let pack := fun (w : Nat) (l : List Nat) => l.foldr (fun x acc => x + 2 ^ w * acc) 0
  let nat1 := fun (l : List Nat) => Val.list (l.toArray.map .nat)
  let D := ptMapT dltC
  let LA : Array (Array Nat) := ((List.range 5).map fun j => liftTab T j).toArray
  let lt := LA.toList.map (·.toList)
  let SAa : Array (Array Nat) := LA.map (sArrT W0)
  let sa := SAa.toList.map (·.toList)
  let AM : Array (Array Nat) := SAa.map fun s => ((List.range 512).map (collAmat s)).toArray
  let amat := fun (j b : Nat) => AM[j]![b]!
  let CT : Array (Array (Array Nat)) := LA.map fun s =>
    ((List.range 512).map fun a => candT T W0 s a).toArray
  let isInv := fun (j a : Nat) => isInvoT CT[j]![a]!
  let KY : Array (Array Nat) := ((List.range 5).map fun j => ((List.range 512).map fun a =>
    ((List.range 512).map fun b => a ^^^ b ^^^ amat j b).foldl min 512).toArray).toArray
  let key := fun (j a : Nat) => KY[j]![a]!
  let rp : List (List Nat) := [1, 3, 19] :: (List.range 4).map fun j =>
    (List.range 512).filter fun a => key (j + 1) a == a && isInv (j + 1) a
  let rd := (List.range 4).map fun j => (List.range 512).map fun a =>
    let c := CT[j + 1]![a]!
    if !isInvoT c then
      2 * ((List.range 693).find? fun x => c[c[x]!]! != x).getD 0 + 1
    else
      let r := key (j + 1) a
      let b := ((List.range 512).find? fun b => (a ^^^ b ^^^ amat (j + 1) b) == r).getD 0
      2 * (b + 512 * r)
  let rr := ((List.range 5).zip rp).flatMap fun (j, reps) => reps.map fun a =>
    let c := CT[j]![a]!
    let sg := sigT F PP P c
    let ds := (List.range 891).map (dVec W sg)
    let bs := pickIndep ds 5
    let pairs := bs.flatMap fun v =>
      let i := ((List.range 891).find? fun i => dVec W sg i == v).getD 0
      [i, sg[i]!]
    let opp := (List.range 891).find? fun i => fB W[sg[i]!]! W[i]!
    let fixp := (List.range 891).find? fun i =>
      (List.range 21).all fun k => c[P[i]![k]!]! == P[i]![k]!
    match opp, fixp with
    | some i, _ => [j, a, 0, i, sg[i]!] ++ pairs
    | none, some i => [j, a, 1, i, 0] ++ pairs
    | none, none => [j, a, 2, 0, 0] ++ pairs
  if rr.any fun r => r.length != 15 then throw "cdStep: fewer than five independent vectors"
  return #[(`LT, nat1 (lt.map (pack 10))), (`FT, .nat (pack 10 (ptMapT frobC).toList)),
    (`DT, .nat (pack 10 D.toList)), (`DI, .nat (pack 10 (invTab D).toList)),
    (`EI, .nat (pack 10 (invTab (compTab D D)).toList)),
    (`SA, .list (sa.toArray.map nat1)), (`RP, .list (rp.toArray.map nat1)),
    (`RD, .list (rd.toArray.map nat1)), (`RR, .list (rr.toArray.map nat1))]

end CertificateChecks.KernelSmithEK
