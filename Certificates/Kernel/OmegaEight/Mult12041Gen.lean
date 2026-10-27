module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverData
public import CFSG.Adapters.ProjectiveSpecialLinear
public meta import CFSG.Certificates.CosetTableShort
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public meta import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public meta import CFSG.Sporadic.SmallOddCore.CheckSpec

namespace CertificateChecks.KernelO8.Mult12041

open CFSG.KC.Eval CFSG.EvenSmallLie.OmegaEight.Cover

public meta def formN (n : Nat) : List Nat → Nat → Nat
  | a :: b :: l, x =>
    let y := formN n (b :: l) x
    if y = a % n then b % n else if y = b % n then a % n else y
  | _, x => x

public meta def relStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "relStep: expected no arguments"
  let n := 240
  let mut TT := 0
  for i in [0:4] do
    let cs := rhoCycles (Fin.ofNat 4 i)
    let f := Array.ofFn (n := n) fun x => cs.foldr (fun c acc => formN n c acc) x.val
    let mut g := Array.replicate n 0
    for x in [0:n] do
      g := g.set! f[x]! x
    for x in [0:n] do
      TT := TT ||| (f[x]! <<< (8 * (2 * i * n + x))) ||| (g[x]! <<< (8 * ((2 * i + 1) * n + x)))
  let RS := rels.map fun w => w.map fun l => 2 * l.1.val + if l.2 then 0 else 1
  return #[(`TT, .nat TT), (`RS, .list (RS.toArray.map fun w => .list (w.toArray.map .nat)))]

end CertificateChecks.KernelO8.Mult12041
