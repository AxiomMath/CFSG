module

public import CFSG.Certificates.Kernel.O8AutSound
public import Certificates.Kernel.OmegaEight.AutChainAP
public import Certificates.Kernel.OmegaEight.AutChainAM
public import Certificates.Kernel.OmegaEight.AutChainOmP
public import Certificates.Kernel.OmegaEight.NatData
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Enum (pidn)

theorem kGenAP : CFSG.KC.Enum.allN 10 (fun j => Nat.beq (AP.S j) (genP NSP NIP j)) = true := by
  quickRfl
theorem kGenOm : CFSG.KC.Enum.allN 8 (fun j => Nat.beq (OmP.S j) (genP NSP NIP j)) = true := by
  quickRfl
theorem kGenAM : CFSG.KC.Enum.allN 11 (fun j => Nat.beq (AM.S j) (genM NSM NIM j)) = true := by
  quickRfl

theorem bitN_eq (x i : ℕ) : bitN x i = (x.testBit i).toNat := by
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

theorem bb_eq (x y i j : ℕ) : bb x y i j = (x.testBit i && y.testBit j).toNat := by
  rw [bb, bitN_eq, bitN_eq]
  cases x.testBit i <;> cases y.testBit j <;> rfl

theorem xor_toNat (a b : Bool) : Nat.xor a.toNat b.toNat = (a ^^ b).toNat := by
  cases a <;> cases b <;> rfl

theorem toNat_beq_one (a : Bool) : (a.toNat == 1) = a := by
  cases a <;> rfl

theorem formP : FormBind false OmegaEight.qNat OmegaEight.bNat := by
  refine ⟨fun v _ => ?_, fun v _ w _ => ?_⟩
  · simp only [q8K, OmegaEight.qNat, bb_eq, xor_toNat, toNat_beq_one, Bool.xor_assoc]
  · simp only [b8K, OmegaEight.bNat, bb_eq, xor_toNat, toNat_beq_one, Bool.xor_assoc]

theorem formM : FormBind true OmegaEightMinus.qNat OmegaEightMinus.bNat := by
  refine ⟨fun v _ => ?_, fun v _ w _ => ?_⟩
  · simp only [q8K, OmegaEightMinus.qNat, bb_eq, bitN_eq, xor_toNat, toNat_beq_one,
      Bool.xor_assoc]
  · simp only [b8K, OmegaEightMinus.bNat, bb_eq, xor_toNat, toNat_beq_one, Bool.xor_assoc]

theorem genArrsP_eq :
    OmegaEight.genArrs = genArrsPG OmegaEight.qNat OmegaEight.bNat OmegaEight.rootPairs := rfl

theorem genArrsM_eq :
    OmegaEightMinus.genArrs = genArrsMG OmegaEightMinus.qNat OmegaEightMinus.bNat
      OmegaEightMinus.gPairs := rfl

theorem psiArrP_eq (y : ℕ) :
    psiArr .plus y = psiArrG 120 OmegaEight.qNat OmegaEight.bNat (bpos .plus) y := rfl

theorem psiArrM_eq (y : ℕ) :
    psiArr .minus y = psiArrG 136 OmegaEightMinus.qNat OmegaEightMinus.bNat (bpos .minus) y := rfl

theorem rootPairs_bind : OmegaEight.rootPairs.length = 8 ∧ ∀ j < 8, ∀ t < 3,
    (OmegaEight.rootPairs.getD j []).getD t (0, 0) =
      (fget RP (6 * j + 2 * t) 8, fget RP (6 * j + 2 * t + 1) 8) := by
  decide +kernel

theorem gPairs_bind : OmegaEightMinus.gPairs.length = 10 ∧
    ∀ j < 10,
      OmegaEightMinus.gPairs.getD j (0, 0) = (fget GP (2 * j) 8, fget GP (2 * j + 1) 8) := by
  decide +kernel

theorem bposP : ∀ j < 6, bpos .plus j = fget 5665569 j 4 := by decide +kernel
theorem bposM : ∀ j < 6, bpos .minus j = fget 4552225 j 4 := by decide +kernel

theorem genAP :
    OmegaEight.genArrs.size = 10 ∧ ∀ j < 10, OmegaEight.genArrs[j]! = unpack 360 9 (AP.S j) := by
  obtain ⟨hs, he⟩ := genP_sound formP kNsP rootPairs_bind
  rw [genArrsP_eq]
  refine ⟨hs, fun j hj => ?_⟩
  rw [he j hj, Nat.eq_of_beq_eq_true (allN_spec kGenAP j hj)]

theorem genOm : (OmegaEight.genArrs.extract 0 8).size = 8 ∧
    ∀ j < 8, (OmegaEight.genArrs.extract 0 8)[j]! = unpack 360 9 (OmP.S j) := by
  obtain ⟨hs, he⟩ := genP_sound formP kNsP rootPairs_bind
  rw [genArrsP_eq]
  refine ⟨by simp [hs], fun j hj => ?_⟩
  have h1 : j < (genArrsPG OmegaEight.qNat OmegaEight.bNat OmegaEight.rootPairs).size := by omega
  have e : ((genArrsPG OmegaEight.qNat OmegaEight.bNat OmegaEight.rootPairs).extract 0 8)[j]! =
      (genArrsPG OmegaEight.qNat OmegaEight.bNat OmegaEight.rootPairs)[j]! := by
    rw [getElem!_pos _ j (by simp [hs]; omega), getElem!_pos _ j h1]
    simp
  rw [e, he j (by omega), Nat.eq_of_beq_eq_true (allN_spec kGenOm j hj)]

theorem genAM : OmegaEightMinus.genArrs.size = 11 ∧
    ∀ j < 11, OmegaEightMinus.genArrs[j]! = unpack 136 8 (AM.S j) := by
  obtain ⟨hs, he⟩ := genM_sound formM kNsM gPairs_bind
  rw [genArrsM_eq]
  refine ⟨hs, fun j hj => ?_⟩
  rw [he j hj, Nat.eq_of_beq_eq_true (allN_spec kGenAM j hj)]

theorem chainAP : ChainOK 360 9 AP.S AP.SI AP.LR AP.TR AP.TRI 18 10 7 AP.BP AP.NS 24
    OmegaEight.autWords OmegaEight.autS (aBaseA .plus) := by
  obtain ⟨hs, he⟩ := pushWords_eq genAP AP.head
  refine ⟨⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩, AP.head, AP.hl,
    by decide, AP.hs⟩
  interval_cases t <;> rfl

theorem chainOmP : ChainOK 360 9 OmP.S OmP.SI OmP.LR OmP.TR OmP.TRI 17 8 7 OmP.BP OmP.NS 24
    OmegaEight.omegaWords OmegaEight.omegaS ((OmegaEight.omegaBase.map Fin.val).toArray) := by
  obtain ⟨hs, he⟩ := pushWords_eq genOm OmP.head
  refine ⟨⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩, OmP.head, OmP.hl,
    by decide, OmP.hs⟩
  interval_cases t <;> rfl

theorem chainAM : ChainOK 136 8 AM.S AM.SI AM.LR AM.TR AM.TRI 19 11 7 AM.BP AM.NS 17
    aWordsMinus aSMinus (aBaseA .minus) := by
  obtain ⟨hs, he⟩ := pushWords_eq genAM AM.head
  refine ⟨⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩, AM.head, AM.hl,
    by decide, AM.hs⟩
  interval_cases t <;> rfl

@[expose] def QW : List (List Int) :=
  [[2, 15, 11], [1, 10, 1, 10], [1, 11, 1, 11], [1, 9, 1, 9], [1, 3, 1, 3], [1]]

theorem kQW : allN 6 (fun j => lettersK 17 (QW.getD j [])) = true := by quickRfl

theorem kAutP :
    autPsiOK 360 9 (fun j => wordK 360 9 (mask 9) (pidn 360 9) OmP.S OmP.SI (QW.getD j []))
    AP.LR AP.TRI AP.BP 7
    (fun y P => andB (siftK 360 9 (mask 9) (360 * 9) (pidn 360 9) OmP.LR OmP.TRI OmP.BP 7 0 P)
      (Nat.beq (Nat.land P (maskN 1080)) (psiK false NSP NIP 120 9 5665569 y))) = true := by
  quickRfl

theorem kAutM :
    autPsiOK 136 8 (fun j => psiK true NSM NIM 136 8 4552225 (pw2 j)) AM.LR AM.TRI AM.BP 7
    (fun y P => Nat.beq P (psiK true NSM NIM 136 8 4552225 y)) = true := by
  quickRfl

theorem psiTT_eq (ε : Eps) {y : ℕ} (hy : y < 64) : psiTT ε y = psiTArrG (aDeg ε) (qtArr ε) y := by
  cases ε <;> simp [psiTT, psiTTabPlus, psiTTabMinus, Array.getD, hy] <;> rfl

theorem autCheckP_eq : autCheck .plus = autCheckG 360 10 OmegaEight.autS (aBaseA .plus)
    OmegaEight.autWords (aSizes .plus) (psiTT .plus) (fun y g =>
      siftA 360 (rawLevels 360 OmegaEight.omegaS ((OmegaEight.omegaBase.map Fin.val).toArray))
        ((OmegaEight.omegaBase.map Fin.val).toArray) 0 g &&
      eqA 120 (OmegaEight.copy0Arr g) (psiArr .plus y)) := rfl

theorem autCheckM_eq : autCheck .minus = autCheckG 136 11 aSMinus (aBaseA .minus) aWordsMinus
    (aSizes .minus) (psiTT .minus) (fun y g => eqA 136 g (psiArr .minus y)) := rfl

theorem cert3373 : (autCheck .plus = true) ∧ (autCheck .minus = true) := by
  rw [autCheckP_eq, autCheckM_eq]
  exact ⟨autP_sound chainAP chainOmP (by decide) (fun y hy => psiTT_eq .plus hy)
      (fun y _ => by rw [psiArrP_eq]; exact psiP_sound formP kNsP bposP y) kQW kAutP,
    autM_sound chainAM (by decide) (fun y hy => psiTT_eq .minus hy)
      (fun y _ => by rw [psiArrM_eq]; exact psiM_sound formM kNsM bposM y) kAutM⟩

end CertificateChecks.KernelO8

end
