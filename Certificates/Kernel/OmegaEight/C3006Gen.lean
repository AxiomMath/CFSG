module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverData
public meta import Certificates.Kernel.OmegaEight.Mult12041Gen
public import Certificates.Kernel.OmegaEight.Mult12041Gen

namespace CertificateChecks.KernelO8.C3006

open CFSG.KC.Eval CFSG.EvenSmallLie.OmegaEight.Cover CertificateChecks.KernelO8.Mult12041

public meta def cycArr (n : Nat) (cs : List (List Nat)) : Array Nat :=
  Array.ofFn (n := n) fun x => cs.foldr (fun c acc => formN n c acc) x.val

public meta def invArr (f : Array Nat) : Array Nat := Id.run do
  let mut g := Array.replicate f.size 0
  for x in [0:f.size] do
    g := g.set! f[x]! x
  return g

public meta def packTab (n w : Nat) (fs : List (Array Nat)) : Nat := Id.run do
  let mut TT := 0
  let mut i := 0
  for f in fs do
    let g := invArr f
    for x in [0:n] do
      TT := TT ||| (f[x]! <<< (w * (2 * i * n + x))) ||| (g[x]! <<< (w * ((2 * i + 1) * n + x)))
    i := i + 1
  return TT

public meta def step3006 (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "step3006: expected no arguments"
  let xs := (List.range 8).map fun r => cycArr 360 (genCycles (Fin.ofNat 8 r))
  let xis := xs.map invArr
  let gcs := (List.range 4).map fun i => genCodes (Fin.ofNat 4 i)
  let aArr := fun (codes : List Int) => Array.ofFn (n := 360) fun x =>
    codes.foldr (fun (z : Int) (y : Nat) =>
      if 0 < z then (xs[z.toNat - 1]!)[y]! else (xis[(-z).toNat - 1]!)[y]!) x.val
  let as := gcs.map aArr
  let rs := (List.range 4).map fun i => cycArr 240 (rhoCycles (Fin.ofNat 4 i))
  return #[(`TX, .nat (packTab 360 9 xs)), (`TA, .nat (packTab 360 9 as)),
    (`TR, .nat (packTab 240 8 rs))]

end CertificateChecks.KernelO8.C3006
