module

public import Certificates.Kernel.SmithL6K.GlueO
public import Certificates.Kernel.SmithL6K.ChecksA
public import Certificates.Kernel.SmithL6K.ChecksQ
public import CFSG.Certificates.Kernel.SmithL6KQSound
public import Certificates.Data.SmithL6IdCheck

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.CollK CFSG.GF2Type.SmithTypeE.LMod
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V)

theorem idChkWt_holds : idChkWt = true := by
  have h0 := wtd_ne0
  rw [List.all_eq_true] at h0
  unfold idChkWt
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq]
  intro i hi
  rw [wtArr_get hi]
  refine ⟨wt_lt20K i, ?_⟩
  have e := h0 (wt i) (by
    rw [wt_eq hi]
    exact getDQ_mem (by rw [wtd_length]; exact hi))
  simpa using e

theorem idChkWtInj_holds : idChkWtInj = true := by
  unfold idChkWtInj
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  intro i hi j hj
  rw [wtArr_get hi, wtArr_get hj]
  by_cases h : i = j
  · exact Or.inl h
  · exact Or.inr fun e => h (wt_inj i hi j hj e)

theorem tcl_apK {p : Nat} (hp : p < 1953) (x : Nat) :
    apK (tcl.getD p []) x = applyCols (tvCols p) x := by
  rw [← tvCols_eq hp, ← applyCols_toArray, Array.toArray_toList]

theorem wtd_getD {j : Nat} (hj : j < 1395) : wtd.getD j 0 = wt j := (wt_eq hj).symm

theorem wmk_getD {j : Nat} (hj : j < 1395) : wmk.getD j 0 = wMask j := (wMask_eq hj).symm

theorem qa_zero : ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
    (∀ s, ∃ p : Fin 1953, p ∈ planeSet 0 ∧ ∃ k : Fin 1395, ¬ Opp 0 k ∧
      v s = tvLin p.val (wtV k) + wtV k) ∧
    ∀ j : Fin 1395, wtV j ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW 0 j = true :=
  qa_sound (fun _ hj => wtd_getD hj) wtd_length (fun _ hj => wmk_getD hj) (fun _ hp => tcl_apK hp)
    p0_planePts qa_ok

theorem cv_zero : ∀ v : V, (∀ p ∈ planeSet 0, tvLin p.val v = v) ↔ v = 0 ∨ v = wtV 0 :=
  cv_sound (wtd_getD (by decide)) (fun _ hp => tcl_apK hp) p0_planePts cv_ok

end CertificateChecks.KernelSmithL6K
