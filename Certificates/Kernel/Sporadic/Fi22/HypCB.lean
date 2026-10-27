module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2067T
public import Certificates.Data.Kernel.Spor.CommBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs
public meta import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.Fitting.CharacteristicP
public meta import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public meta import CFSG.Walter.JRFacts
public import CFSG.Walter.JRFacts

public section

namespace CertificateChecks.KernelSpor.Fi22CB

open CFSG.EvenSporadicStandard.HypOne.Fi22

meta def compA (p q : Array Nat) : Array Nat := q.map fun i => p[i]!

meta def invA (p : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate p.size 0
  for i in [0:p.size] do
    r := r.set! p[i]! i
  return r

meta def wordA (G : Array (Array Nat)) (w : List Int) : Array Nat :=
  w.foldl (fun (r : Array Nat) (z : Int) =>
    compA r (if z > 0 then G[z.toNat - 1]! else invA G[(-z).toNat - 1]!)) (Array.range 3510)

meta def powA (p : Array Nat) (e : Nat) : Array Nat :=
  (List.range e).foldl (fun r _ => compA r p) (Array.range 3510)

meta def lettersOf (k : Nat) (gs : List Nat) (hw : List Int) (e : Nat) (cw : List Int) :
    Array (Array Nat) :=
  let G := (gs.map fun j => (hypTbl j).map (·.toNat)).toArray
  let h1 := powA (wordA G hw) e
  let c := wordA G cw
  let h2 := compA c (compA h1 (invA c))
  #[h1, h2, CFSG.Sporadic.FischerOddCore.fi22ExtArr (21 + k), invA h1, invA h2]

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def pow5 (p : Nat) : Nat := Fi22X.c p (Fi22X.c p (Fi22X.c p (Fi22X.c p p)))

@[expose] noncomputable def lettersOK (M : Nat → Nat) (t : Nat) : Bool :=
  bAnd(allN 5 (fun z => Fi22X.cn (M z)),
  bAnd(Nat.beq (M 2) t,
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) (M 0) (M 3),
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) (M 1) (M 4),
  bAnd(Fi22X.siftP (M 0), bAnd(Fi22X.siftP (M 1),
  bAnd(Nat.beq (Fi22X.c (M 0) t) (Fi22X.c t (M 0)),
  bAnd(Nat.beq (Fi22X.c (M 1) t) (Fi22X.c t (M 1)),
  bAnd(Nat.beq (pow5 (M 0)) (pidn 3510 12), Nat.beq (pow5 (M 1)) (pidn 3510 12))))))))))

@[expose] noncomputable def baseChk (M : Nat → Nat) (B : List CFSG.KC.CommBase.BaseRec)
    (PF ZF DF : Nat) : Bool :=
  CFSG.KC.CommBase.commBaseOK 3510 12 (mask 12) M 5 B PF ZF DF

end CertificateChecks.KernelSpor.Fi22CB

end
