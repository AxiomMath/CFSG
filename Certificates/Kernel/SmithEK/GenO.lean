module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.SMod20UaStab

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th.Native

meta def bfsRecs (n m : Nat) (f : Nat → Nat → Nat) (roots : List Nat) : List Nat := Id.run do
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

public meta def oStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "oStep: expected no arguments"
  let P := uaPts
  let T := tvTabs
  let F := uaFlags P
  let PP := uaPtPlanes P
  let W0 := P[0]!
  let G := (tvGens ()).toList.map fun c => (uPos ())[c]!
  let J := G.map fun p => (List.range 891).map fun j =>
    uaPlaneOf F PP fun m => ap T[p]! P[j]![m]!
  let Ja := J.toArray.map List.toArray
  let pack := fun (w : Nat) (l : List Nat) => l.foldr (fun x acc => x + 2 ^ w * acc) 0
  let PLs := P.toList.map Array.toList
  let sig := stabWords.map (stabSig T W0)
  let fS := fun g j => uaPlaneOf F PP fun m => stabAp T stabWords[g]! P[j]![m]!
  let meet := fun j => uaMeet W0 P[j]!
  let ds := [21, 5, 1, 0].map fun c => ((List.range 891).find? fun j => meet j == c).getD 0
  let nat1 := fun (l : List Nat) => Val.list (l.toArray.map .nat)
  return #[(`PL, .list (PLs.toArray.map nat1)), (`PLP, .nat (pack 210 (PLs.map (pack 10)))),
    (`G, nat1 G), (`J, .list (J.toArray.map nat1)), (`JP, nat1 (J.map (pack 10))),
    (`R, nat1 (bfsRecs 891 46 (fun g u => Ja[g]![u]!) [0])),
    (`SW, nat1 (stabWords.toList.map fun w => w.1 + 1024 * w.2)),
    (`SG, .list (sig.map fun s => nat1 s.toList)),
    (`UR, nat1 (bfsRecs 512 sig.size (fun g u => collAmat sig[g]! u) [1, 3, 19])),
    (`DS, nat1 ds), (`DR, nat1 (bfsRecs 891 sig.size fS ds)), (`CO, nat1 uaCo.toList)]

end CertificateChecks.KernelSmithEK
