module

public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.Spor.CommCent
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SuzCenterInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SuzCenterInputs
import CFSG.Certificates.Kernel.Common.Harness
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

namespace CertificateChecks.KernelSpor.SuzCI

open CFSG.EvenSporadicStandard.HypOne.Suz CFSG.EvenSporadicStandard.Solomon78

meta def compM (p q : Array Nat) : Array Nat := q.map fun i => p[i]!

meta def invM (p : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate p.size 0
  for i in [0:p.size] do
    r := r.set! p[i]! i
  return r

meta def lettersOf (i : Nat) (gs : List Nat) : Array (Array Nat) :=
  let G := (gs.map fun j => (hypTbl j).map (·.toNat)).toArray
  #[G[0]!, G[1]!, CFSG.Sporadic.SuzOddCore.tArr i, invM G[0]!, invM G[1]!]

meta def umovM : Array (Array Nat) :=
  (Array.range 8).map fun k => (umovTbl k).map (·.toNat)

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.CommBase

@[expose] noncomputable def c (p q : Nat) : Nat := pcomp 1782 11 (mask 11) p q

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 1782 11 (mask 11) (1782 * 11) p

@[expose] noncomputable def inv (p : Nat) : Nat := pinvS 1782 11 (mask 11) p

@[expose] noncomputable def lettersOK (M : Nat → Nat) (T : Nat) : Bool :=
  bAnd(allN 5 (fun z => cn (M z)),
  bAnd(Nat.beq (M 2) T,
  bAnd(permOK 1782 11 (mask 11) (1782 * 11) (M 0) (M 3),
  bAnd(permOK 1782 11 (mask 11) (1782 * 11) (M 1) (M 4),
  bAnd(Suz2306.sift (M 0), bAnd(Suz2306.sift (M 1),
  bAnd(Nat.beq (c (M 0) T) (c T (M 0)),
  Nat.beq (c (M 1) T) (c T (M 1)))))))))

@[expose] def Ts : List Nat := [nat_lit 42, nat_lit 54]

@[expose] noncomputable def tsOK : Bool :=
  allN 2 (fun i => memL (fixCnt 1782 11 (mask 11) (SuzTP i)) Ts)

@[expose] noncomputable def centChk (M : Nat → Nat) (B : List BaseRec) (PF ZF DF RF : Nat) : Bool :=
  centFixOK 1782 11 (mask 11) M 5 2 B PF ZF DF RF Ts

@[expose] noncomputable def umovK (L T T' : Nat) : Bool :=
  bAnd(cn L, bAnd(cn (inv L), bAnd(permOK 1782 11 (mask 11) (1782 * 11) L (inv L),
  bAnd(Suz2306.sift L, bAnd(cn T, bAnd(cn T',
  strictB (c (c L T) (inv L)) fun C => Nat.beq (c C T') (c T' C)))))))

end CertificateChecks.KernelSpor.SuzCI

end
