module

public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowSylTests
public import Certificates.Kernel.LocalComp.HeSyl.Check16
public import Certificates.Kernel.LocalComp.HeSyl.Words
public import CFSG.Certificates.Kernel.PermToolSound
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.AS81.HeSylow CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def PC1I (j : Nat) : Nat := W.PI.getD j 0

@[expose] noncomputable def RS (i c : Nat) : Nat := ([W.R0, W.R1, W.R2, W.R3, W.R4].getD i []).getD c 0

@[expose] noncomputable def NB (i : Nat) : Nat := [2, 2, 9, 4, 2].getD i 0

@[expose] noncomputable def WG (i : Nat) : Nat := RS i 0

@[expose] noncomputable def ckW (i c : Nat) : Bool :=
  Nat.beq (wordK 8330 14 (mask 14) (RS i (c + 1)) PC1 PC1I (((heSylWords.getD i []).drop (8 * c)).take 8))
    (RS i c)

@[expose] noncomputable def enK (i : Nat) : Bool :=
  Nat.beq (RS i (NB i)) (pidn 8330 14) && Nat.ble (heSylWords.getD i []).length (8 * NB i)

@[expose] noncomputable def ck0 (c : Nat) : Bool := ckW 0 c
@[expose] noncomputable def ck1 (c : Nat) : Bool := ckW 1 c
@[expose] noncomputable def ck2 (c : Nat) : Bool := ckW 2 c
@[expose] noncomputable def ck3 (c : Nat) : Bool := ckW 3 c
@[expose] noncomputable def ck4 (c : Nat) : Bool := ckW 4 c

@[expose] noncomputable def agreeK (g : Nat) (σ : Array Nat) : Bool :=
  strictB g fun g => allN 16 fun k => Nat.beq (pg 14 (mask 14) g heSylPts[k]!) heSylPts[σ[k]!]!

end CertificateChecks.KernelLC.HeSyl

#kon_slices CertificateChecks.KernelLC.HeSyl.ck0 0 2
#kon_join CertificateChecks.KernelLC.HeSyl.ck0All CertificateChecks.KernelLC.HeSyl.ck0 2
#kon_slices CertificateChecks.KernelLC.HeSyl.ck1 0 2
#kon_join CertificateChecks.KernelLC.HeSyl.ck1All CertificateChecks.KernelLC.HeSyl.ck1 2
#kon_slices CertificateChecks.KernelLC.HeSyl.ck2 0 9
#kon_join CertificateChecks.KernelLC.HeSyl.ck2All CertificateChecks.KernelLC.HeSyl.ck2 9
#kon_slices CertificateChecks.KernelLC.HeSyl.ck3 0 4
#kon_join CertificateChecks.KernelLC.HeSyl.ck3All CertificateChecks.KernelLC.HeSyl.ck3 4
#kon_slices CertificateChecks.KernelLC.HeSyl.ck4 0 2
#kon_join CertificateChecks.KernelLC.HeSyl.ck4All CertificateChecks.KernelLC.HeSyl.ck4 2
#kon_slices CertificateChecks.KernelLC.HeSyl.enK 0 5
#kon_join CertificateChecks.KernelLC.HeSyl.enAll CertificateChecks.KernelLC.HeSyl.enK 5

namespace CertificateChecks.KernelLC.HeSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow CertificateChecks.KernelLC.HeFix

theorem ckAll {i : Nat} (hi : i < 5) : ∀ c < NB i, ckW i c = true := by
  match i, hi with
  | 0, _ => exact ck0All
  | 1, _ => exact ck1All
  | 2, _ => exact ck2All
  | 3, _ => exact ck3All
  | 4, _ => exact ck4All

theorem wordVal {i : Nat} (hi : i < 5) :
    wordK 8330 14 (mask 14) (pidn 8330 14) PC1 PC1I (heSylWords.getD i []) = WG i := by
  have he := enAll i hi
  unfold enK at he
  rw [Bool.and_eq_true] at he
  exact wordK_chain (Nat.le_of_ble_eq_true he.2) (Nat.eq_of_beq_eq_true he.1)
    fun c hc => Nat.eq_of_beq_eq_true (ckAll hi c hc)

theorem kPerm : allN 9 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (PC1 j) (PC1I j)) = true := by
  quickRfl

theorem kPermC : allN 9 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (PC1 j)
    (pinvS 8330 14 (mask 14) (PC1 j))) = true := by quickRfl

theorem kLetters : allN 5 (fun i => lettersK 9 (heSylWords.getD i [])) = true := by quickRfl

theorem kSz : szOK 8330 14 = true := by quickRfl

theorem kPts : allN 16 (fun k => Nat.blt heSylPts[k]! 8330) = true := by quickRfl

theorem kInc : allN 15 (fun k => Nat.blt heSylPts[k]! heSylPts[k + 1]!) = true := by quickRfl

theorem kA0 : agreeK (WG 0) (heSyl16.getD 0 #[]) = true := by quickRfl
theorem kA1 : agreeK (WG 1) (heSyl16.getD 1 #[]) = true := by quickRfl
theorem kA2 : agreeK (WG 2) (heSyl16.getD 2 #[]) = true := by quickRfl
theorem kA3 : agreeK (WG 3) (heSyl16.getD 3 #[]) = true := by quickRfl
theorem kA4 : agreeK (WG 4) (heSyl16.getD 4 #[]) = true := by quickRfl

theorem letters_get {j : Nat} (hj : j < 9) : heSylLetters[j]! = unpack 8330 14 (PC1 j) := by
  rw [heSylLetters, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact heC1_eq hj

theorem lettersS : heSylLetters.size = 9 ∧ ∀ j < 9, heSylLetters[j]! = unpack 8330 14 (PC1 j) :=
  ⟨by simp [heSylLetters], fun _ hj => letters_get hj⟩

theorem wordFacts {i : Nat} (hi : i < 5) :
    heSylGen i = unpack 8330 14 (WG i) ∧ lettersOK 9 (heSylWords.getD i []) = true := by
  have h : wordEqK 8330 14 (mask 14) (pidn 8330 14) PC1 PC1I 9 (heSylWords.getD i []) (WG i) =
      true := by
    unfold wordEqK
    rw [wordVal hi, Nat.beq_refl, kSz, allN_spec kLetters i hi]
  exact wordEqK_sound lettersS kPerm h

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem agree_of {g : Nat} {σ : Array Nat} (h : agreeK g σ = true) :
    agreeOK 16 (unpack 8330 14 g) heSylPts σ = true := by
  unfold agreeK at h
  rw [strictB_app] at h
  unfold agreeOK
  rw [allLt_iff]
  intro k hk
  have hp : heSylPts[k]! < 8330 := Nat.blt_eq.mp (allN_spec kPts k hk)
  rw [unpack_getElem!]
  simp only [hp, ↓reduceIte, CFSG.KC.HexaK.beq_nat]
  exact allN_spec h k hk

theorem sylCheck8330S_true : sylCheck8330S = true := by
  unfold sylCheck8330S
  simp only [Bool.and_eq_true]
  refine ⟨⟨by quickRfl, allLt_iff.2 fun i hi => (wordFacts hi).2⟩, allLt_iff.2 fun j hj => ?_⟩
  rw [letters_get hj]
  exact validA_unpack (allN_spec kPermC j hj)

theorem valid16 {i : Nat} (hi : i < 5) : validA 16 (heSyl16.getD i #[]) = true := by
  have kb := kBind
  simp only [Bool.and_eq_true] at kb
  have hb := binds_of_check (by unfold bindK at kb; exact kb.1.1.1.1)
  have kp := kPermG
  simp only [Bool.and_eq_true] at kp
  have hng : HeSylX.ng = 5 := rfl
  have e : heSyl16.getD i #[] = heSyl16.toArray[i]! := by interval_cases i <;> rfl
  rw [e, hb.2 i (by rw [hng]; exact hi)]
  exact validA_unpack (allN_spec kp.1.1.1.1 i (by rw [hng]; exact hi))

theorem sylCheckRestrict_true : sylCheckRestrict = true := by
  unfold sylCheckRestrict
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨by quickRfl, by quickRfl⟩, allLt_iff.2 fun k hk => ?_⟩, allLt_iff.2 fun k hk => ?_⟩,
    allLt_iff.2 fun i hi => ?_⟩
  · exact decide_eq_true (Nat.blt_eq.mp (allN_spec kPts k hk))
  · exact decide_eq_true (Nat.blt_eq.mp (allN_spec kInc k hk))
  rw [Bool.and_eq_true, (wordFacts hi).1]
  refine ⟨valid16 hi, agree_of ?_⟩
  interval_cases i
  exacts [kA0, kA1, kA2, kA3, kA4]

end CertificateChecks.KernelLC.HeSyl

end
