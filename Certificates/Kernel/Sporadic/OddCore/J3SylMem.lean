module

public import Certificates.Kernel.Sporadic.OddCore.J3HypSyl
public import Certificates.Kernel.Sporadic.OddCore.SqrtK26102
public import Certificates.Kernel.Sporadic.OddCore.S16J3K27810
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

namespace CertificateChecks.KernelSpor.J3SylMem

meta def hypInvM : Array (Array Nat) :=
  (List.range 12).toArray.map fun k => CFSG.Monster.B.Co2.Native.invCand 6156
    (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.EvenSporadicStandard.HypOne.J3.hypTbl k))

end CertificateChecks.KernelSpor.J3SylMem

#kmisc_packarrs CertificateChecks.KernelSpor.J3HypI CertificateChecks.KernelSpor.J3SylMem.hypInvM 13

namespace CertificateChecks.KernelSpor.J3SylMem

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.SqrtK26102 (j3W)
open CertificateChecks.KernelSpor.S16J3 (pc cK iK outJ3)

theorem hypInv : allN 12 (fun k => iK (J3HypP k) (J3HypI k)) = true := by
  quickRfl

@[expose] noncomputable def cm (X t : Nat) : Bool := Nat.beq (pc X t) (pc t X)

@[expose] noncomputable def wu (wd : List Int) (X : Nat) : Bool := j3W wd (pc X (J3CentP 0))

theorem s_hyp0 : wu [2, 1, 5, 1, 2, 4, 2, 4, 2, 2, 1, 3, 4, 3, 4, 3] (J3HypP 0) = true := by
  quickRfl
theorem s_hyp1 : j3W [4] (J3HypP 1) = true := by quickRfl
theorem s_hyp2 : j3W [1, 5, 5, 1, 3, 5, 1, 4, 5] (J3HypP 2) = true := by quickRfl
theorem s_hyp3 : j3W [4, 3, 2, 1, 2, 2, 5, 1, 3, 3, 5, 1, 3, 4, 5, 5] (J3HypP 3) = true := by
  quickRfl
theorem s_hyp4 : j3W [1] (J3HypP 4) = true := by quickRfl
theorem s_hyp5 : wu [4, 3, 1, 2, 1, 3, 5, 1, 2, 4, 1, 5, 3, 1, 4, 5, 5] (J3HypP 5) = true := by
  quickRfl
theorem s_hyp6 : wu [3, 1, 2, 4, 1, 2, 2, 3, 1, 5, 5, 3, 3] (J3HypP 6) = true := by quickRfl
theorem s_hyp7 : j3W [4, 3, 2, 1, 2, 2, 5, 4, 3, 5] (J3HypP 7) = true := by quickRfl
theorem s_hyp8 : j3W [1] (J3HypP 8) = true := by quickRfl
theorem s_hyp9 : j3W [5, 4, 3, 1, 5, 4, 3, 4] (J3HypP 9) = true := by quickRfl
theorem s_hyp10 : j3W [4] (J3HypP 10) = true := by quickRfl
theorem s_hyp11 : j3W [4, 3, 3, 2, 1, 3, 1, 2, 5, 4, 3, 5, 3, 3] (J3HypP 11) = true := by
  quickRfl
theorem s_cent1 : j3W [1] (J3CentP 1) = true := by quickRfl
theorem s_cent2 : j3W [4, 3, 2, 1, 2, 2, 5, 4, 3, 5] (J3CentP 2) = true := by quickRfl
theorem s_cent3 : j3W [2, 4, 2, 4, 1, 5, 3, 2, 1, 5, 5, 1, 3, 3, 5] (J3CentP 3) = true := by
  quickRfl
theorem s_cent4 : wu [4, 2, 3, 1, 2, 3, 1, 2, 3, 3, 1, 5, 5, 3, 4] (J3CentP 4) = true := by
  quickRfl
theorem s_cent5 : j3W [3, 2, 1, 2, 2, 5, 1, 3, 3, 5, 1, 3, 5] (J3CentP 5) = true := by quickRfl
theorem s_cent6 : j3W [5, 4, 3, 1, 5, 4, 3, 4] (J3CentP 6) = true := by quickRfl
theorem s_cent7 : wu [4, 2, 3, 1, 2, 3, 1, 2, 1, 5, 3, 3, 3, 3] (J3CentP 7) = true := by quickRfl
theorem s_cent8 : j3W [2, 3, 1, 2, 3, 1, 2, 1, 3, 3, 3, 4, 5, 3, 5, 5] (J3CentP 8) = true := by
  quickRfl
theorem s_cent10 : j3W [1] (J3CentP 10) = true := by quickRfl
theorem s_cent11 : j3W [2, 1, 2, 1, 3, 2, 4, 2, 2, 3, 1, 3, 5, 1, 5, 3, 1, 4, 5, 5] (J3CentP 11) =
    true := by quickRfl
theorem s_cent12 : j3W [4, 3, 2, 1, 2, 2, 5, 4, 3, 5] (J3CentP 12) = true := by quickRfl
theorem s_cent13 : j3W [5, 5, 2, 1, 5, 1, 2, 2, 1, 3, 5, 3, 1, 5, 5] (J3CentP 13) = true := by
  quickRfl
theorem s_cent14 : j3W [4, 3, 3, 3, 5, 3, 3, 4, 5] (J3CentP 14) = true := by quickRfl
theorem s_cent21 : wu [3, 1, 2, 4, 1, 2, 2, 3, 1, 5, 5, 3, 3] (J3CentP 21) = true := by quickRfl
theorem s_cent22 : j3W [1] (J3CentP 22) = true := by quickRfl
theorem s_cent23 : j3W [4, 3, 2, 1, 2, 2, 5, 4, 3, 5] (J3CentP 23) = true := by quickRfl
theorem s_cent24 : j3W [3, 1, 2, 4, 1, 2, 1, 2, 4, 5, 3, 1, 3, 1, 4] (J3CentP 24) = true := by
  quickRfl

theorem s_neg : (!j3W [4] (J3HypP 2)) = true := by quickRfl

theorem c_t0 : bAnd(allN 14 (fun k => cm (J3CentP (Nat.add k 1)) (J3CentP 9)),
    allN 4 (fun k => cm (J3HypP k) (J3CentP 9))) = true := by
  quickRfl

theorem c_t1 : bAnd(allN 4 (fun k => cm (J3CentP (Nat.add k 21)) (J3CentP 21)),
    allN 4 (fun k => cm (J3HypP (Nat.add k 4)) (J3CentP 21))) = true := by
  quickRfl

theorem c_neg : (!cm (J3CentP 0) (J3HypP 2)) = true := by quickRfl

theorem o_z0 : outJ3 [] (J3HypP 0) = true := by quickRfl
theorem o_t1 : outJ3 [-2, -1, -2, -4, -2, -4, -3, -3, -2] (J3CentP 21) = true := by quickRfl

@[expose] noncomputable def invo (X : Nat) : Bool :=
  bAnd(Nat.beq (pc X X) (pidn 6156 13), bIf(Nat.beq X (pidn 6156 13), false, true))

@[expose] noncomputable def e8K (a b c : Nat) : Bool :=
  bAnd(cm a b, bAnd(cm a c, bAnd(cm b c, bAnd(invo a, bAnd(invo b, bAnd(invo c,
    bAnd(invo (pc a b), bAnd(invo (pc a c), bAnd(invo (pc b c), invo (pc (pc a b) c))))))))))

theorem e8_ok : e8K (J3HypP 8) (J3HypP 9) (J3HypP 10) = true := by quickRfl

theorem e8_neg : (!e8K (J3HypP 8) (J3HypP 9) (J3HypP 11)) = true := by quickRfl

theorem four_ok : invo (pc (pc (pc (J3HypP 11) (J3CentP 21)) (J3HypI 11)) (J3CentI 21)) = true := by
  quickRfl

theorem four_neg :
    (!invo (pc (pc (pc (J3CentP 21) (J3CentP 21)) (J3CentI 21)) (J3CentI 21))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.J3SylMem

end
