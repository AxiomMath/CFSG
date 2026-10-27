module

public import Certificates.Kernel.TwoHS.Sig
public import Certificates.Kernel.TwoHS.HYOpsGlue

public section

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS CFSG.KS.MulH
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.HSMultiplier

theorem sig_sq (i : Fin 6) : Nat.beq (WK (sigWord (sigWords.getD i.val []))) (HY.F i.val) = true :=
  match i with
  | ⟨0, _⟩ => sig_sq0
  | ⟨1, _⟩ => sig_sq1
  | ⟨2, _⟩ => sig_sq2
  | ⟨3, _⟩ => sig_sq3
  | ⟨4, _⟩ => sig_sq4
  | ⟨5, _⟩ => sig_sq5

theorem sig_parts (i : Fin 6) :
    sigY i = tabT (CFSG.KS.Raw.unpack 11200 14 (SG i)) ∧ Cn (SG i) ∧
      sigYI i = tabT (CFSG.KS.Raw.unpack 11200 14 (SGI i)) ∧ Cn (SGI i) ∧
      permOK 11200 (sigY i) = true ∧ invOK 11200 (sigY i) (sigYI i) = true :=
  word_inv (lettersOK_getD sigWords_letters i.val)
    (List.all_eq_true.1 sig_inv i (List.mem_finRange i))

theorem sigY_eq (i : Fin 6) : sigY i = tabT (CFSG.KS.Raw.unpack 11200 14 (SG i)) ∧ Cn (SG i) :=
  ⟨(sig_parts i).1, (sig_parts i).2.1⟩

theorem sigYI_eq (i : Fin 6) :
    sigYI i = tabT (CFSG.KS.Raw.unpack 11200 14 (SGI i)) ∧ Cn (SGI i) :=
  ⟨(sig_parts i).2.2.1, (sig_parts i).2.2.2.1⟩

theorem sigmaOK_true : sigmaOK = true := by
  have c1 : (List.finRange 6).all (fun i => permOK 11200 (sigY i) && invOK 11200 (sigY i) (sigYI i))
      = true := by
    rw [List.all_eq_true]
    intro i _
    rw [(sig_parts i).2.2.2.2.1, (sig_parts i).2.2.2.2.2]
    rfl
  have c2 : hsRels.all (fun r => (List.finRange 6).all fun i =>
      commTT 11200 (sigY i) (evalW 11200 sigY sigYI r)) = true := by
    rw [List.all_eq_true]
    intro r hr
    rw [List.all_eq_true]
    intro i _
    obtain ⟨e, c⟩ := evalW_eq sigY_eq sigYI_eq r
    rw [e, (sigY_eq i).1, commTT_eq (sigY_eq i).2 c]
    have hr' : r ∈ hsCoxeter ∨ r ∈ hsExtra := List.mem_append.1 hr
    rcases hr' with h | h
    · exact List.all_eq_true.1 (List.all_eq_true.1 sig_rels_cox r h) i (List.mem_finRange i)
    · exact List.all_eq_true.1 (List.all_eq_true.1 sig_rels_extra r h) i (List.mem_finRange i)
  have c3 : (List.finRange 6).all (fun i =>
      tblEq 11200 (evalW 11200 sigY sigYI (hsCommWord i)) (sigY i)) = true := by
    rw [List.all_eq_true]
    intro i _
    obtain ⟨e, c⟩ := evalW_eq sigY_eq sigYI_eq (hsCommWord i)
    rw [e, (sigY_eq i).1, tblEq_eq c (sigY_eq i).2]
    exact List.all_eq_true.1 sig_comm i (List.mem_finRange i)
  have c4 : (List.finRange 6).all (fun i =>
      tblEq 11200 (wordTbl 11200 harYs (sigWord (sigWords.getD i.val []))) (harY i)) = true := by
    rw [List.all_eq_true]
    intro i _
    obtain ⟨e, c⟩ := wordTbl_eq (lettersOK_sigWord (sigWords.getD i.val []))
    rw [e, harY_eq i, tblEq_eq c (hy i.isLt).1]
    exact sig_sq i
  have c5 : (fixCnt 11200 (wordTbl 11200 harYs outerWord) !=
      fixCnt 11200 (wordTbl 11200 harYs (sigWord outerWord))) = true := by
    obtain ⟨e1, c1⟩ := wordTbl_eq (wd := outerWord) (by decide)
    obtain ⟨e2, c2⟩ := wordTbl_eq (lettersOK_sigWord outerWord)
    rw [e1, e2, fixCnt_eq c1, fixCnt_eq c2]
    exact sig_fix
  unfold sigmaOK
  simp only [c1, c2, c3, c4, c5, Bool.and_self]

end CFSG.KD.TwoHS

end
