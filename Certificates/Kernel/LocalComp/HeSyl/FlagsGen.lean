module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.LocalComp.BfsGen
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData
public import Certificates.Kernel.LocalComp.BfsGen

namespace CertificateChecks.KernelLC.HeSyl

open CFSG.KC.Eval CFSG.KS.RawGen

public meta def flagStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "flagStep: expected no arguments"
  let gens := CFSG.ComponentClassification.AS81.HeSylow.heSyl16.toArray
  let z := CFSG.ComponentClassification.AS81.HeSylow.heSylZ16
  let (pts, _) := CFSG.KC.BfsGen.search 16 5 gens
  if pts.size != 1024 then throw "flagStep: the enumeration does not have 1024 points"
  let idn := Array.ofFn (n := 16) fun i => i.val
  let mut fz := 0
  let mut f1 := 0
  for i in [0:pts.size] do
    let q := comp 16 pts[i]! pts[i]!
    if q == idn || q == z then fz := fz ||| (1 <<< i)
    if q == idn then f1 := f1 ||| (1 <<< i)
  return #[(`FZ, .nat fz), (`F1, .nat f1)]

end CertificateChecks.KernelLC.HeSyl
