module

public import Certificates.Kernel.Om2K.Base
public import Certificates.Kernel.Om2K.ChecksW

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab)

theorem wordOK_all : ∀ c < 9, wordOKc c = true := by
  intro c hc
  interval_cases c
  · exact wordOKc0
  · exact wordOKc1
  · exact wordOKc2
  · exact wordOKc3
  · exact wordOKc4
  · exact wordOKc5
  · exact wordOKc6
  · exact wordOKc7
  · exact wordOKc8

theorem word_ok {w : List Nat} (hw : w ∈ allWordsY) : okK (wYK w) = true := by
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 hw
  rw [kLen] at hk
  have h := allN_spec (wordOK_all (k / 32) (by omega)) (k % 32) (Nat.mod_lt _ (by norm_num))
  have e2 : Nat.add (Nat.mul 32 (k / 32)) (k % 32) = k := Nat.div_add_mod k 32
  rw [e2, List.getD_eq_getElem _ _ (by rw [kLen]; exact hk), e] at h
  exact h

theorem words_k : wordsCheckY (reflTab ()) = true := by
  unfold wordsCheckY
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, by decide⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    have hs : (genY (reflTab ())).size = 8 := by simp [genY]
    have hi8 : i < 8 := hs ▸ hi
    rw [← getElem!_pos _ i hi, genY_get hi8, ← Nat.eq_of_beq_eq_true (allN_spec kGY i hi8)]
    exact validA_ok (L_ok (by omega))
  · rw [List.all_eq_true]
    intro w hw
    have hl := List.all_eq_true.1 kLetters w hw
    refine Bool.and_eq_true_iff.2 ⟨hl, ?_⟩
    have hl' : ∀ l ∈ w, l < 16 := fun l hm => by
      unfold wordYOK at hl
      exact of_decide_eq_true (List.all_eq_true.1 hl l hm)
    rw [(wY_eq w hl').1]
    exact validA_ok (word_ok hw)

end CertificateChecks.KernelOm2

end
