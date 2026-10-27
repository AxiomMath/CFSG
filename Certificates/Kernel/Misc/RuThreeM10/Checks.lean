module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.FiveLocK
public import Certificates.Kernel.B3S3.Gen
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public meta import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Misc.RuThreeM10.Keys
public meta import Certificates.Kernel.Misc.RuThreeM10.Keys
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib
public import Mathlib

set_option maxRecDepth 400000

#kb3_enum CertificateChecks.KernelMisc.RuThreeM10.EA
  CFSG.EvenSporadicStandard.RuStd.S2.ruThreeM11 CertificateChecks.KernelMisc.RuThreeM10.k11 11 4
#kb3_enum CertificateChecks.KernelMisc.RuThreeM10.ET
  CFSG.EvenSporadicStandard.RuStd.S2.ruThreeM CertificateChecks.KernelMisc.RuThreeM10.k11 11 4

public section

namespace CertificateChecks.KernelMisc.RuThreeM10

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
  CFSG.KC.B3S3K

@[expose] noncomputable def invK (p : Nat) : Bool :=
  bAnd(!Nat.beq p (pidn 11 4), Nat.beq (cm 11 4 p p) (pidn 11 4))

@[expose] noncomputable def stabK : Bool :=
  allN 3 fun k => bAnd(memK EA.N EA.T (ET.G k), Nat.beq (pg 4 (mask 4) (ET.G k) 0) 0)

@[expose] noncomputable def coverK : Bool :=
  allN EA.N fun i => bIf(Nat.beq (pg 4 (mask 4) (EA.T i) 0) 0, memK ET.N ET.T (EA.T i), true)

@[expose] noncomputable def centerK : Bool :=
  allN ET.N fun k =>
    bIf(allN 3 fun l => CFSG.KC.FiveLocK.commK 11 4 (ET.T k) (ET.G l),
      Nat.beq (ET.T k) (pidn 11 4), true)

@[expose] noncomputable def oddK : Bool :=
  allN ET.N fun k => bIf(Nat.beq (ET.T k) (pidn 11 4), true,
    bIf(CFSG.KC.LQT.P.anyN 16 fun e => invK (pw 11 4 (ET.T k) e), true,
      CFSG.KC.LQT.P.anyN ET.N fun g => invK (cm 11 4 (ET.T k) (cj 11 4 (ET.T g) (ET.T k)))))

theorem szOK' : szOK 11 4 = true := by quickRfl

theorem bA : ∀ j < 2, arrBind ruThreeM11[j]! 11 4 (EA.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bT : ∀ j < 3, arrBind ruThreeM[j]! 11 4 (ET.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem pA : allN 2 (fun j => permB 11 4 (EA.G j)) = true := by quickRfl

theorem pT : allN 3 (fun j => permB 11 4 (ET.G j)) = true := by quickRfl

theorem n0 : Nat.beq EA.N 7920 = true ∧ Nat.beq ET.N 720 = true ∧ Nat.beq EA.ng 2 = true ∧
    Nat.beq ET.ng 3 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem kStab : stabK = true := by quickRfl

theorem kCover : coverK = true := by quickRfl

theorem kCenter : centerK = true := by quickRfl

theorem kOdd : oddK = true := by quickRfl

theorem negOdd : (!(CFSG.KC.LQT.P.anyN 16 fun e => invK (pw 11 4 (pidn 11 4) e))) = true := by
  quickRfl

theorem negCenter : (!allN 3 fun l => CFSG.KC.FiveLocK.commK 11 4 (ET.G 1) (ET.G l)) = true := by
  quickRfl

end CertificateChecks.KernelMisc.RuThreeM10

end
