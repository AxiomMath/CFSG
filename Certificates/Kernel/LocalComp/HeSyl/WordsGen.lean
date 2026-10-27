module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Kernel.Sporadic.RawGen

namespace CertificateChecks.KernelLC.HeSyl

open CFSG.KC.Eval CFSG.KS.RawGen

public meta def unpk (P : Nat) : Array Nat :=
  Array.ofFn (n := 8330) fun i => (P >>> (14 * i.val)) &&& 16383

public meta def wordStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 9 then throw "wordStep: expected 9 arguments"
  let mut L : Array (Array Nat) := #[]
  for a in args do
    match a with
    | .nat v => L := L.push (unpk v)
    | _ => throw "wordStep: expected natural numbers"
  let LI := L.map (inv 8330)
  let idn := Array.ofFn (n := 8330) fun i => i.val
  let letter := fun (z : Int) => if z > 0 then L[z.toNat - 1]! else LI[(-z).toNat - 1]!
  let mut outs : Array (Lean.Name × Val) := #[(`PI, .list (LI.map fun t => .nat (pack 14 t)))]
  for i in [0:5] do
    let wd := (CFSG.ComponentClassification.AS81.HeSylow.heSylWords.getD i []).toArray
    let nb := (wd.size + 7) / 8
    let mut vals : Array Val := #[]
    for c in [0:nb + 1] do
      let v := (wd.extract (8 * c) wd.size).foldr (fun z acc => comp 8330 (letter z) acc) idn
      vals := vals.push (.nat (pack 14 v))
    outs := outs.push (Lean.Name.mkSimple s!"R{i}", .list vals)
  return outs

end CertificateChecks.KernelLC.HeSyl
