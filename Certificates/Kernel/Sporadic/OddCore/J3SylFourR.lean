module

public import Certificates.Kernel.Sporadic.OddCore.J3HypSyl
public import Certificates.Kernel.Sporadic.OddCore.J3OutSyl
public import Certificates.Data.Kernel.Spor.FiveK
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
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
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.J3SylFourR

meta def z0InvM : Array (Array Nat) :=
  #[CFSG.Monster.B.Co2.Native.invCand 6156
    (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.EvenSporadicStandard.HypOne.J3.hypTbl 0))]

end CertificateChecks.KernelSpor.J3SylFourR

#kmisc_packarrs CertificateChecks.KernelSpor.J3Z0I CertificateChecks.KernelSpor.J3SylFourR.z0InvM 13

namespace CertificateChecks.KernelSpor.J3SylFourR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CertificateChecks.KernelSpor

theorem r0Inv : invEqK 6156 13 (mask 13) (6156 * 13) (J3HypP 0) (J3Z0I 0) = true := by
  quickRfl

@[expose] noncomputable def cgR (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 5), J3CentP (Nat.add l (nat_lit 10)), J3HypP (nat_lit 0))

@[expose] noncomputable def cgRI (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 5), J3CentI (Nat.add l (nat_lit 10)), J3Z0I (nat_lit 0))

@[expose] noncomputable def rowR (e s : Nat) : Bool :=
  strictB (pcomp 6156 13 (mask 13) s s) (fun s2 =>
    bIf(bAnd(Nat.beq (pcomp 6156 13 (mask 13) s2 s2) e,
        bAnd(bIf(Nat.beq s2 e, false, true), bIf(Nat.beq s e, false, true))),
      fiveTopK 6156 13 (mask 13) cgR cgRI 6 2 s, true))

@[expose] noncomputable def r0Row (i : Nat) : Bool :=
  strictB (pidn 6156 13) (fun e => strictB (J3XS.T i) (fun s => rowR e s))

theorem r0Five0 : slK 256 r0Row 0 16 = true := by quickRfl

theorem r0Five1 : slK 256 r0Row 16 16 = true := by quickRfl

theorem r0Five2 : slK 256 r0Row 32 16 = true := by quickRfl

theorem r0Five3 : slK 256 r0Row 48 16 = true := by quickRfl

theorem r0Five4 : slK 256 r0Row 64 16 = true := by quickRfl

theorem r0Five5 : slK 256 r0Row 80 16 = true := by quickRfl

theorem r0Five6 : slK 256 r0Row 96 16 = true := by quickRfl

theorem r0Five7 : slK 256 r0Row 112 16 = true := by quickRfl

theorem r0Five8 : slK 256 r0Row 128 16 = true := by quickRfl

theorem r0Five9 : slK 256 r0Row 144 16 = true := by quickRfl

theorem r0Five10 : slK 256 r0Row 160 16 = true := by quickRfl

theorem r0Five11 : slK 256 r0Row 176 16 = true := by quickRfl

theorem r0Five12 : slK 256 r0Row 192 16 = true := by quickRfl

theorem r0Five13 : slK 256 r0Row 208 16 = true := by quickRfl

theorem r0Five14 : slK 256 r0Row 224 16 = true := by quickRfl

theorem r0Five15 : slK 256 r0Row 240 16 = true := by quickRfl

theorem r0FiveNeg1 : (!fiveTopK 6156 13 (mask 13) cgR cgRI 6 0 (J3XS.T 5)) = true := by quickRfl

theorem r0FiveNeg2 : (!fiveTopK 6156 13 (mask 13) cgR cgRI 6 2 (pidn 6156 13)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.J3SylFourR

end
