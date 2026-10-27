module

public import Certificates.Kernel.LocalComp.HeRSLP
public import Certificates.Kernel.LocalComp.HeRChain
public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.Certificates.Kernel.HeRKSound
public import CFSG.Certificates.Kernel.PermSLPSound
import CFSG.Certificates.Kernel.Common.Harness
import all Certificates.Data.HePresData

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PermSLP CFSG.KC.HeRK
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.AS81.HePres.Native CertificateChecks.KernelLC.HeFix
open CertificateChecks.KernelLC

theorem kGP : allN 8 (fun i => permOK 8330 14 (mask 14) (8330 * 14) (HRW i) (HRI i)) = true := by
  quickRfl

theorem kK1 : heRK1 HRW HRI heRWords heRWitWord = true := by quickRfl

theorem kK2_0 : heRK2 HRW HRI heRWords heRCentWords 0 = true := by quickRfl
theorem kK2_1 : heRK2 HRW HRI heRWords heRCentWords 1 = true := by quickRfl
theorem kK2_2 : heRK2 HRW HRI heRWords heRCentWords 2 = true := by quickRfl
theorem kK2_3 : heRK2 HRW HRI heRWords heRCentWords 3 = true := by quickRfl

theorem kK2 : ∀ k < 4, heRK2 HRW HRI heRWords heRCentWords k = true := by
  intro k hk
  match k, hk with
  | 0, _ => exact kK2_0
  | 1, _ => exact kK2_1
  | 2, _ => exact kK2_2
  | 3, _ => exact kK2_3

theorem kK3_0 : heRK3 HRW HRI HeRC.S heRCentWords 0 = true := by quickRfl
theorem kK3_1 : heRK3 HRW HRI HeRC.S heRCentWords 1 = true := by quickRfl

theorem kK3 : ∀ j < 2, heRK3 HRW HRI HeRC.S heRCentWords j = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact kK3_0
  | 1, _ => exact kK3_1

theorem kK4 : heRK4 HeRC.S HeRC.SI (fun j => heRChainWords[j]!) = true := by quickRfl

theorem kPS : allN 9 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (HeRC.S j) (HeRC.SI j)) = true := by
  quickRfl

theorem kB : (Nat.beq heRChainBaseArr.size 3 &&
    allN 3 fun t => Nat.beq heRChainBaseArr[t]! (pg 14 (mask 14) HeRC.BP t)) = true := by quickRfl

theorem kOrd : Nat.beq (((List.range 3).map fun i => rcnt (HeRC.LR i)).prod) 80640 = true := by
  quickRfl

theorem seeds : heSeedArrs.size = 2 ∧ ∀ j < 2, heSeedArrs[j]! = unpack 8330 14 (L2 j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => simpa [heSeedArrs, L2_0] using heGen_eq (k := 0) (by decide)
  | 1, _ => simpa [heSeedArrs, L2_1] using heGen_eq (k := 1) (by decide)

theorem cnL2 : ∀ j, cn (L2 j) = true := by
  have h := kCn
  simp only [Bool.and_eq_true] at h
  intro j
  match j with
  | 0 => exact h.1.1.1.1
  | 1 => exact h.1.1.1.2
  | _ + 2 => exact h.2

theorem cnL2I : ∀ j, cn (L2I j) = true := by
  have h := kCn
  simp only [Bool.and_eq_true] at h
  intro j
  match j with
  | 0 => exact h.1.1.2
  | 1 => exact h.1.2
  | _ + 2 => exact h.2

theorem word_eq {i : Nat} (hi : i < 8) :
    wordA 8330 heSeedArrs (rawInvs 8330 heSeedArrs) (hePiHeWords.getD i []) =
      unpack 8330 14 (HRW i) := by
  have he := toAll i hi
  unfold toR at he
  rw [bAnd_iff, bAnd_iff] at he
  obtain ⟨ht, hz, hl⟩ := he
  have hid : cn (pidn 8330 14) = true := by
    have h := kId
    rw [Bool.and_eq_true] at h
    exact h.1
  have hw : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (WR i) = HRW i :=
    slp_word cnL2 cnL2I hid ltAll ruAll (by norm_num) ht
  have hq : wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 (WR i) (HRW i) = true := by
    unfold wordEqK
    rw [hz, hl, hw, Nat.beq_refl]
  rw [gw_eq]
  exact (wordEqK_sound seeds kPL2 hq).1

theorem g8_size : heGenArrs8.size = 8 := by simp [heGenArrs8]

theorem g8_eq {i : Nat} (hi : i < 8) : heGenArrs8[i]! = unpack 8330 14 (HRW i) := by
  rw [getElem!_pos heGenArrs8 i (by rw [g8_size]; exact hi)]
  simp only [heGenArrs8, List.getElem_toArray, List.getElem_map, List.getElem_range]
  exact word_eq hi

theorem facts : heGenArrsOK = true ∧ heRInvolOK = true ∧ heRWitOK = true ∧ heRCentOK = true ∧
    heRStrong.size = 9 ∧ (∀ j < 9, heRStrong[j]! = unpack 8330 14 (HeRC.S j)) ∧
    (eqA 8330 heRStrong[0]! heRChainOrig[0]! && eqA 8330 heRStrong[1]! heRChainOrig[1]!) = true := by
  have h := heRK_sound g8_size (fun i hi => g8_eq hi) (fun i hi => allN_spec kGP i hi) kK1 kK2 kK3 kK4
  rw [heGenArrsOK_eq, heRInvolOK_eq, heRWitOK_eq, heRCentOK_eq, heRStrong_eq, heRChainOrig_eq]
  exact h

theorem binds : Binds 8330 14 HeRC.S 9 3 HeRC.BP heRStrong heRChainBaseArr := by
  have kb := kB
  rw [Bool.and_eq_true] at kb
  obtain ⟨-, -, -, -, hsz, hS, -⟩ := facts
  exact ⟨by norm_num, by norm_num, by norm_num, hsz, hS, Nat.eq_of_beq_eq_true kb.1,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec kb.2 t ht)⟩

theorem chain : rawChainOK 8330 (heRStrong.extract 0 2) heRStrong heRChainBaseArr heRChainWords 1 =
    true := by
  have hw : heRChainWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 heRDerivs := by
    decide +kernel
  rw [hw]
  exact rawChainK_sound (NS := HeRC.NS) (CH := 1) (chunks := 1) binds HeRC.head HeRC.hl
    (by decide) HeRC.hs

theorem order : (rawOrbitSizes 8330 heRStrong heRChainBaseArr).prod = 80640 := by
  rw [rawOrbitSizesK_sound binds kPS HeRC.hl]
  exact Nat.eq_of_beq_eq_true kOrd

end CertificateChecks.KernelLC.HeR

end
