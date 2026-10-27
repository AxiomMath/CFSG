module

public import Certificates.Kernel.Sporadic.OddCore.J3HypSyl
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.FiveK
public import Certificates.Data.Kernel.Spor.MulHF
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
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

namespace CertificateChecks.KernelSpor.J3SylFourR1

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 6156

meta def idsM : Array (Array Nat) := Array.replicate 4 idM

meta def sM : Array (Array Nat) := sgR1.map natArr

end CertificateChecks.KernelSpor.J3SylFourR1

#kmulh CertificateChecks.KernelSpor.J3R1S 6156 13 CertificateChecks.KernelSpor.J3SylFourR1.idsM
  CertificateChecks.KernelSpor.J3SylFourR1.sM CertificateChecks.KernelSpor.J3SylFourR1.idM 32

namespace CertificateChecks.KernelSpor.J3SylFourR1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

theorem r1Base : bAnd(szOK 6156 13, bAnd(cK (pidn 6156 13),
    bAnd(allN 4 (fun j => bAnd(cK (J3R1S.GI j), bAnd(Nat.beq (J3R1S.GI j) (J3HypP (Nat.add j 4)),
      Nat.beq (J3R1S.G j) (pidn 6156 13)))),
    bAnd(Nat.beq J3R1S.cnt 32, penumHdK (pidn 6156 13) J3R1S.cnt 32 J3R1S.T J3R1S.PL)))) =
      true := by
  quickRfl

theorem r1Enum : penumSlK 6156 13 (mask 13) (6156 * 13) true J3R1S.G J3R1S.GI 4 J3R1S.cnt J3R1S.T
    J3R1S.PL J3R1S.POS J3R1S.SRT J3R1S.SRI 0 J3R1S.cnt = true := by quickRfl

theorem r1Sort : slK J3R1S.cnt (hsortPtKF 6156 13 (mask 13) J3R1S.cnt J3R1S.T J3R1S.HS J3R1S.HSI)
    0 J3R1S.cnt = true := by quickRfl

theorem r1Sort_neg :
    hsortPtKF 6156 13 (mask 13) J3R1S.cnt (fun _ => 0) J3R1S.HS J3R1S.HSI 0 = false := by
  decide +kernel

@[expose] noncomputable def cgR1 (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 3), J3CentP (Nat.add l (nat_lit 22)), J3CentP (nat_lit 21))

@[expose] noncomputable def cgR1I (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 3), J3CentI (Nat.add l (nat_lit 22)), J3CentI (nat_lit 21))

@[expose] noncomputable def rowR1 (e s : Nat) : Bool :=
  strictB (pcomp 6156 13 (mask 13) s s) (fun s2 =>
    bIf(bAnd(Nat.beq (pcomp 6156 13 (mask 13) s2 s2) e,
        bAnd(bIf(Nat.beq s2 e, false, true), bIf(Nat.beq s e, false, true))),
      fiveTopK 6156 13 (mask 13) cgR1 cgR1I 4 2 s, true))

@[expose] noncomputable def r1Row (i : Nat) : Bool :=
  strictB (pidn 6156 13) (fun e => strictB (J3R1S.T i) (fun s => rowR1 e s))

theorem r1Five0 : slK 32 r1Row 0 16 = true := by quickRfl

theorem r1Five1 : slK 32 r1Row 16 16 = true := by quickRfl

theorem r1FiveNeg1 : (!fiveTopK 6156 13 (mask 13) cgR1 cgR1I 4 1 (J3R1S.T 23)) = true := by
  quickRfl

theorem r1FiveNeg2 : (!fiveTopK 6156 13 (mask 13) cgR1 cgR1I 4 2 (pidn 6156 13)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.J3SylFourR1

end
