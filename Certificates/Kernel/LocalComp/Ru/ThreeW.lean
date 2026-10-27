module

public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Certificates.Kernel.LocalCompThreeWPSound
public import Certificates.Kernel.LocalComp.Ru.WChecks
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.RuAutInner
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.RuW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LocalComp.ThreeWP
open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.RuSchreier
open CertificateChecks.KernelSporSch.RuG

theorem kG0 : Nat.beq (TG 0) C0 = true := by quickRfl
theorem kG1 : Nat.beq (TG 1) C1 = true := by quickRfl
theorem kG2 : Nat.beq (TG 2) C0I = true := by quickRfl
theorem kG3 : Nat.beq (TG 3) C1I = true := by quickRfl

theorem tg0 : TG 0 = C0 := Nat.eq_of_beq_eq_true kG0
theorem tg1 : TG 1 = C1 := Nat.eq_of_beq_eq_true kG1
theorem tg2 : TG 2 = C0I := Nat.eq_of_beq_eq_true kG2
theorem tg3 : TG 3 = C1I := Nat.eq_of_beq_eq_true kG3

theorem qW_eq : ruQWord = qW := by decide

theorem yW_eq : ruYWord = yW := by decide

theorem cC0 : canonK 4060 12 (mask 12) (4060 * 12) C0 = true := by quickRfl

theorem cC1 : canonK 4060 12 (mask 12) (4060 * 12) C1 = true := by quickRfl

theorem letters_eq (z : Int) : ruLetterTab z = arrTable (unpack 4060 12 (letP z)) := by
  unfold ruLetterTab letP
  split_ifs
  · rw [tg0, c0_eq]
  · rw [tg1, c1_eq]

theorem letters_canon (z : Int) : canonK 4060 12 (mask 12) (4060 * 12) (letP z) = true := by
  unfold letP
  split_ifs
  · rw [tg0]
    exact cC0
  · rw [tg1]
    exact cC1

theorem kSz : szOK 4060 12 = true := by quickRfl

theorem q_eq : ruQTab = arrTable (unpack 4060 12 (TQY 0)) :=
  by
  rw [ruQTab, qW_eq]
  exact powT_wordT_sound kSz (fun z _ => letters_eq z) (fun z _ => letters_canon z) kQ

theorem y_eq : ruYTab = arrTable (unpack 4060 12 (TQY 1)) :=
  by
  rw [ruYTab, yW_eq]
  exact powT_wordT_sound kSz (fun z _ => letters_eq z) (fun z _ => letters_canon z) kY

theorem g0 : ruCTab[0]! = arrTable ruC0A := by
  rw [ruCTab, getElem!_pos _ 0 (by simp)]
  rfl

theorem g1 : ruCTab[1]! = arrTable ruC1A := by
  rw [ruCTab, getElem!_pos _ 1 (by simp)]
  rfl

theorem gi0 : ruCInvTab[0]! = arrTable (ruInv ruC0A) := by
  rw [ruCInvTab, getElem!_pos _ 0 (by simp)]
  rfl

theorem gi1 : ruCInvTab[1]! = arrTable (ruInv ruC1A) := by
  rw [ruCInvTab, getElem!_pos _ 1 (by simp)]
  rfl

theorem gP0 : gP 0 = C0 := tg0
theorem gP1 : gP 1 = C1 := tg1
theorem giP0 : giP 0 = C0I := tg2
theorem giP1 : giP 1 = C1I := tg3

theorem three : threeWitnessOK 4060 ruCTab ruCInvTab ruQTab ruYTab 400 = true := by
  refine threeWitnessOK_of_P (k := 2) (G := gP) (GI := giP) (E := TE) (R := TR) kSz
    ⟨rfl, fun l hl => ?_⟩ ⟨rfl, fun l hl => ?_⟩ (fun l hl => ?_) q_eq y_eq (by norm_num) kHead kRows
    kComm
  · match l, hl with
    | 0, _ => rw [g0, gP0, c0_eq]
    | 1, _ => rw [g1, gP1, c1_eq]
  · match l, hl with
    | 0, _ => rw [gi0, giP0, (inv_of c0_eq pC0).1]
    | 1, _ => rw [gi1, giP1, (inv_of c1_eq pC1).1]
  · match l, hl with
    | 0, _ => rw [gP0, giP0]; exact pC0
    | 1, _ => rw [gP1, giP1]; exact pC1

end CertificateChecks.KernelLC.RuW
