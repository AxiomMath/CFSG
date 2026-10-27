module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LargeExtraspecial.S14SMKTransCheck

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th.Native

meta def ntBfs (n m : Nat) (f : Nat → Nat → Nat) (roots : List Nat) : List Nat := Id.run do
  let mut seen := Array.replicate n false
  for r in roots do
    seen := seen.set! r true
  let mut queue : Array Nat := roots.toArray
  let mut recs : Array Nat := #[]
  let mut head := 0
  while head < queue.size do
    let u := queue[head]!
    head := head + 1
    for g in [0:m] do
      let v := f g u
      if v < n && !seen[v]! then
        seen := seen.set! v true
        queue := queue.push v
        recs := recs.push (v + 1024 * u + 1048576 * g)
  return recs.toList

public meta def ntStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "ntStep: expected no arguments"
  let T := tvTabs
  let W0 := uaPts[0]!
  let I := collInvs collS2 (collMeet collS2)
  let pack := fun (w : Nat) (l : List Nat) => l.foldr (fun x acc => x + 2 ^ w * acc) 0
  let F := I.toList.map fun s => pack 5 s.toList
  let Fa := F.toArray
  let idx := fun (p : Nat) => (Fa.findIdx? (· == p)).getD 675
  let rt := (List.range 4).map fun j => pack 5 (sArrT W0 (liftTab T (j + 1))).toList
  let ri := rt.map idx
  if ri.any (· ≥ 675) then throw "ntStep: a root is not an admissible involution"
  let sg := stabWords.map (stabSig T W0)
  let sr := stabWords.map fun w => stabSig T W0 (w.2, w.1)
  let f := fun g u => idx (pack 5 (collComp (collComp sg[g]! I[u]!) sr[g]!).toList)
  let tr := ntBfs 675 stabWords.size f ri
  if tr.length + ri.length != 675 then throw s!"ntStep: forest reaches {tr.length + ri.length}"
  let nat1 := fun (l : List Nat) => Val.list (l.toArray.map .nat)
  return #[(`FP, .nat (pack 105 F)), (`RT, nat1 rt), (`RI, nat1 ri),
    (`SWR, nat1 (stabWords.toList.map fun w => w.2 + 1024 * w.1)),
    (`SR, .list (sr.map fun s => nat1 s.toList)), (`TR, nat1 tr)]

end CertificateChecks.KernelSmithEK
