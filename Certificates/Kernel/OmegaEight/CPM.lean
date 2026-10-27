module

public import CFSG.Certificates.Kernel.O8CPMSound
public import Certificates.Kernel.OmegaEight.Aut
public import Certificates.Kernel.OmegaEight.CPChains
public import Certificates.Kernel.OmegaEight.Forms
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitConeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
  CFSG.EvenSmallLie.OmegaEight.CPrimeModel CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Enum (pidn permOK)

theorem sigCheck_eq (ε : Eps) : sigCheck ε = sigCheckG (deg ε) (sigArr ε) (psiArr ε)
    (CFSG.EvenSmallLie.OmegaEight.CPrime.reflRows ε (n0 ε)) (uArr ε) (uS ε) (uBaseA ε) := by
  cases ε <;> rfl

theorem wArr_eq : wArr = wArrG OmegaEight.genArrs[8]! OmegaEight.genArrs[9]! := by
  funext j
  match j with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | _ + 5 => rfl

theorem cosetCheck_eq : cosetCheck = cosetCheckG OmegaEight.genArrs[8]! OmegaEight.genArrs[9]!
    OmegaEight.autS (aBaseA .plus) OmegaEight.omegaS ((OmegaEight.omegaBase.map Fin.val).toArray) := by
  unfold cosetCheck cosetCheckG
  rw [wArr_eq]
  rfl

theorem minusCheck_eq : minusCheck = minusCheckG OmegaEightMinus.genArrs[10]!
    OmegaEightMinus.omegaS (lBaseA .minus) := rfl

theorem uSP_0 : (uS .plus)[0]! = unpack 120 9 (UP.S 0) := by decide +kernel
theorem uSP_1 : (uS .plus)[1]! = unpack 120 9 (UP.S 1) := by decide +kernel
theorem uSP_2 : (uS .plus)[2]! = unpack 120 9 (UP.S 2) := by decide +kernel
theorem uSP_3 : (uS .plus)[3]! = unpack 120 9 (UP.S 3) := by decide +kernel
theorem uSP_4 : (uS .plus)[4]! = unpack 120 9 (UP.S 4) := by decide +kernel
theorem uSP_5 : (uS .plus)[5]! = unpack 120 9 (UP.S 5) := by decide +kernel
theorem uSP_6 : (uS .plus)[6]! = unpack 120 9 (UP.S 6) := by decide +kernel
theorem uSP_7 : (uS .plus)[7]! = unpack 120 9 (UP.S 7) := by decide +kernel
theorem uSP_8 : (uS .plus)[8]! = unpack 120 9 (UP.S 8) := by decide +kernel
theorem uSP_9 : (uS .plus)[9]! = unpack 120 9 (UP.S 9) := by decide +kernel
theorem uSP_10 : (uS .plus)[10]! = unpack 120 9 (UP.S 10) := by decide +kernel
theorem uSP_11 : (uS .plus)[11]! = unpack 120 9 (UP.S 11) := by decide +kernel

theorem uSP_bind : ∀ j < 12, (uS .plus)[j]! = unpack 120 9 (UP.S j) := by
  intro j hj
  interval_cases j
  exacts [uSP_0, uSP_1, uSP_2, uSP_3, uSP_4, uSP_5, uSP_6, uSP_7, uSP_8,
    uSP_9, uSP_10, uSP_11]

theorem uSM_0 : (uS .minus)[0]! = unpack 136 8 (UM.S 0) := by decide +kernel
theorem uSM_1 : (uS .minus)[1]! = unpack 136 8 (UM.S 1) := by decide +kernel
theorem uSM_2 : (uS .minus)[2]! = unpack 136 8 (UM.S 2) := by decide +kernel
theorem uSM_3 : (uS .minus)[3]! = unpack 136 8 (UM.S 3) := by decide +kernel
theorem uSM_4 : (uS .minus)[4]! = unpack 136 8 (UM.S 4) := by decide +kernel
theorem uSM_5 : (uS .minus)[5]! = unpack 136 8 (UM.S 5) := by decide +kernel
theorem uSM_6 : (uS .minus)[6]! = unpack 136 8 (UM.S 6) := by decide +kernel
theorem uSM_7 : (uS .minus)[7]! = unpack 136 8 (UM.S 7) := by decide +kernel
theorem uSM_8 : (uS .minus)[8]! = unpack 136 8 (UM.S 8) := by decide +kernel
theorem uSM_9 : (uS .minus)[9]! = unpack 136 8 (UM.S 9) := by decide +kernel
theorem uSM_10 : (uS .minus)[10]! = unpack 136 8 (UM.S 10) := by decide +kernel
theorem uSM_11 : (uS .minus)[11]! = unpack 136 8 (UM.S 11) := by decide +kernel

theorem uSM_bind : ∀ j < 12, (uS .minus)[j]! = unpack 136 8 (UM.S j) := by
  intro j hj
  interval_cases j
  exacts [uSM_0, uSM_1, uSM_2, uSM_3, uSM_4, uSM_5, uSM_6, uSM_7, uSM_8,
    uSM_9, uSM_10, uSM_11]

theorem levelsUP : LevelsK 120 9 UP.S UP.SI UP.LR UP.TR UP.TRI 12 12 5 UP.BP [] (uS .plus)
    (uBaseA .plus) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, rfl, uSP_bind, rfl, fun t ht => ?_⟩, UP.head,
    UP.hl⟩
  interval_cases t <;> rfl

theorem levelsUM : LevelsK 136 8 UM.S UM.SI UM.LR UM.TR UM.TRI 12 12 3 UM.BP [] (uS .minus)
    (uBaseA .minus) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, rfl, uSM_bind, rfl, fun t ht => ?_⟩, UM.head,
    UM.hl⟩
  interval_cases t <;> rfl

theorem kGenLm : CFSG.KC.Enum.allN 10 (fun j => Nat.beq (LMn.S j) (genM NSM NIM j)) = true := by
  quickRfl

theorem genLm : (OmegaEightMinus.genArrs.extract 0 10).size = 10 ∧
    ∀ j < 10, (OmegaEightMinus.genArrs.extract 0 10)[j]! = unpack 136 8 (LMn.S j) := by
  obtain ⟨hs, he⟩ := genM_sound formM kNsM gPairs_bind
  rw [genArrsM_eq]
  refine ⟨by simp [hs], fun j hj => ?_⟩
  have h1 : j < (genArrsMG OmegaEightMinus.qNat OmegaEightMinus.bNat OmegaEightMinus.gPairs).size := by
    omega
  have e : ((genArrsMG OmegaEightMinus.qNat OmegaEightMinus.bNat OmegaEightMinus.gPairs).extract 0
      10)[j]! = (genArrsMG OmegaEightMinus.qNat OmegaEightMinus.bNat OmegaEightMinus.gPairs)[j]! := by
    rw [getElem!_pos _ j (by simp [hs]; omega), getElem!_pos _ j h1]
    simp
  rw [e, he j (by omega), Nat.eq_of_beq_eq_true (allN_spec kGenLm j hj)]

theorem levelsLm : LevelsK 136 8 LMn.S LMn.SI LMn.LR LMn.TR LMn.TRI 18 10 7 LMn.BP
    OmegaEightMinus.omegaWords OmegaEightMinus.omegaS (lBaseA .minus) := by
  obtain ⟨hs, he⟩ := pushWords_eq genLm LMn.head
  refine ⟨⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩, LMn.head, LMn.hl⟩
  interval_cases t <;> rfl

@[expose] noncomputable def SGP : Nat := Nat.land (AP.S 9) (maskN 1080)

theorem sigP_bind : sigArr .plus = unpack 120 9 SGP := by decide +kernel
theorem reflP_bind : CFSG.EvenSmallLie.OmegaEight.CPrime.reflRows .plus (n0 .plus) =
    decR (reflRowsK QP 12) := by decide +kernel
theorem reflM_bind : CFSG.EvenSmallLie.OmegaEight.CPrime.reflRows .minus (n0 .minus) =
    decR (reflRowsK QM 4) := by decide +kernel
theorem uArrP_bind : ∀ k < 6, uArr .plus k = unpack 120 9 (UP.S (6 + k)) := by
  intro k hk
  rw [← uSP_bind (6 + k) (by omega)]
  interval_cases k <;> rfl

theorem uArrM_bind : ∀ k < 6, uArr .minus k = unpack 136 8 (UM.S (6 + k)) := by
  intro k hk
  rw [← uSM_bind (6 + k) (by omega)]
  interval_cases k <;> rfl

theorem kSigP : sigOK 120 9 SGP (fun y => psiK false NSP NIP 120 9 5665569 y) (fun k => UP.S (6 + k))
    (reflRowsK QP 12) UP.LR UP.TRI UP.BP 5 = true := by quickRfl
theorem kSigM : sigOK 136 8 (AM.S 10) (fun y => psiK true NSM NIM 136 8 4552225 y)
    (fun k => UM.S (6 + k)) (reflRowsK QM 4) UM.LR UM.TRI UM.BP 3 = true := by quickRfl
theorem kCoset : cosetOK (AP.S 8) (AP.S 9) (AP.SI 8) (AP.SI 9) AP.LR AP.TRI AP.BP OmP.LR OmP.TRI
    OmP.BP = true := by quickRfl
theorem kMinusR : minusOK (AM.S 10) LMn.LR LMn.TRI LMn.BP = true := by quickRfl
theorem kMinusP : permOK 136 8 (mask 8) (136 * 8) (AM.S 10) (AM.S 10) = true := by quickRfl

theorem cert3780 : (sigCheck .plus = true) ∧ (sigCheck .minus = true) ∧ (cosetCheck = true)
    ∧ (minusCheck = true) := by
  rw [sigCheck_eq, sigCheck_eq, cosetCheck_eq, minusCheck_eq]
  refine ⟨sig_sound levelsUP sigP_bind (fun y _ => by rw [psiArrP_eq]; exact psiP_sound formP kNsP bposP y)
      reflP_bind uArrP_bind kSigP,
    sig_sound levelsUM (genAM.2 10 (by norm_num))
      (fun y _ => by rw [psiArrM_eq]; exact psiM_sound formM kNsM bposM y) reflM_bind uArrM_bind kSigM,
    coset_sound ⟨chainAP.1, chainAP.2.1, chainAP.2.2.1⟩ ⟨chainOmP.1, chainOmP.2.1, chainOmP.2.2.1⟩
      (genAP.2 8 (by norm_num)) (genAP.2 9 (by norm_num)) kCoset,
    minus_sound levelsLm (genAM.2 10 (by norm_num)) kMinusP kMinusR⟩

end CertificateChecks.KernelO8

end
