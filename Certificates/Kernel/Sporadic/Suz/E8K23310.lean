module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.Suz.Order2306
public import Certificates.Data.Kernel.PkPow
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SuzInputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SuzInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.GroupTheory.Fitting.CharacteristicP
meta import CFSG.GroupTheory.LocalCores.Components
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzHypT CFSG.EvenSporadicStandard.HypOne.Suz.hypHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzHypT CFSG.EvenSporadicStandard.HypOne.Suz.hypHex
  3 1782 11 10

namespace CertificateChecks.KernelSpor.Suz23310

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow

@[expose] noncomputable def c (p q : Nat) : Nat := pcomp 1782 11 (mask 11) p q

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 1782 11 (mask 11) (1782 * 11) p

@[expose] noncomputable def X : Nat := ppw 1782 11 (SuzHypT.F 7) 4

@[expose] noncomputable def W : Nat := c (SuzHypT.F 7) (c (SuzHypT.F 9) (SuzHypT.F 6))

@[expose] noncomputable def Y : Nat := c W W

@[expose] noncomputable def Z : Nat := c (SuzHypT.F 8) (c X (SuzHypT.F 8))

@[expose] noncomputable def fixK (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i s => nIf(Nat.beq (pg 11 (mask 11) p i) i, Nat.succ s, s)) 1782

@[expose] noncomputable def invK (p : Nat) : Bool :=
  bAnd(cn p, bAnd(invEqK 1782 11 (mask 11) (1782 * 11) p p,
    bAnd(Nat.beq (ppw 1782 11 p 2) (pidn 1782 11),
    bAnd(bIf(Nat.beq (ppw 1782 11 p 1) (pidn 1782 11), false, true), Nat.beq (fixK p) 54))))

@[expose] noncomputable def e8K (x y z : Nat) : Bool :=
  bAnd(Suz2306.sift x, bAnd(Suz2306.sift y, bAnd(Suz2306.sift z,
  bAnd(Nat.beq (c x y) (c y x), bAnd(Nat.beq (c x z) (c z x), bAnd(Nat.beq (c y z) (c z y),
  bAnd(invK x, bAnd(invK y, bAnd(invK z, bAnd(invK (c x y), bAnd(invK (c x z), bAnd(invK (c y z),
    invK (c (c x y) z)))))))))))))

theorem base23310 : bAnd(szOK 1782 11, bAnd(cn (pidn 1782 11), bAnd(cn (SuzHypT.F 6),
    bAnd(cn (SuzHypT.F 7), bAnd(cn (SuzHypT.F 8), cn (SuzHypT.F 9)))))) = true := by
  quickRfl

theorem k23310 : e8K X Y Z = true := by
  quickRfl

theorem k23310_neg : e8K (ppw 1782 11 (SuzHypT.F 7) 2) Y Z = false := by
  decide +kernel

end CertificateChecks.KernelSpor.Suz23310

end
