module

public import Certificates.Kernel.L34Cov.Words
public import CFSG.Certificates.Kernel.L34Cov.CodesSound
public import Certificates.Data.GrSLitL34FactsRealCheck

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC.L34Cov CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

theorem getD_ofList (C : List (List ℕ)) (k : ℕ) :
    (C.map fun w => String.ofList (w.map decC)).getD k "" =
      String.ofList ((C.getD k []).map decC) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C[k]? <;> rfl

theorem codesOK_getD {C : List (List ℕ)} (h : C.all codesOK = true) (k : ℕ) :
    codesOK (C.getD k []) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : C[k]? with
  | none => rfl
  | some w => exact List.all_eq_true.1 h w (List.mem_of_getElem? hk)

theorem tw_eq (k : ℕ) : tw k = (TwC.codes.getD k []).map decL ∧
    codesOK (TwC.codes.getD k []) = true := by
  have hc := codesOK_getD codes_k.2.1 k
  refine ⟨?_, hc⟩
  rw [tw, TwC.eq, getD_ofList, parseWord_ofList hc]

theorem uA_eq (i : ℕ) : uA i = (UAC.codes.getD i []).map decL ∧
    codesOK (UAC.codes.getD i []) = true := by
  have hc := codesOK_getD codes_k.2.2.2.1 i
  refine ⟨?_, hc⟩
  have e : (realRepU.getD i ("", "")).1 = (realRepU.map Prod.fst).getD i "" := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases realRepU[i]? <;> rfl
  rw [uA, e, UAC.eq, getD_ofList, parseWord_ofList hc]

theorem uB_eq (i : ℕ) : uB i = (UBC.codes.getD i []).map decL ∧
    codesOK (UBC.codes.getD i []) = true := by
  have hc := codesOK_getD codes_k.2.2.2.2.2 i
  refine ⟨?_, hc⟩
  have e : (realRepU.getD i ("", "")).2 = (realRepU.map Prod.snd).getD i "" := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases realRepU[i]? <;> rfl
  rw [uB, e, UBC.eq, getD_ofList, parseWord_ofList hc]

end CertificateChecks.KernelL34Cov

end
