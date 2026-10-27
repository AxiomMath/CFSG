module

public import Certificates.Kernel.Ivk8McL.Wt5254
public import Certificates.Kernel.Sporadic.OddCore.McLTwoF
public import CFSG.Certificates.Kernel.Ivk8CentralNSound

public section

namespace CertificateChecks.KernelIvk8McLWt

open CFSG.KC.Enum CFSG.KC.YoshQ CFSG.KC.Ivk8N CFSG.Sporadic.Recognition.McLAS
  CertificateChecks.KernelSpor CFSG.KS.MulH CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem dims : Dims 275 9 := ⟨by decide, by decide, by decide, by decide⟩

theorem cnt_eq : McLTwoS.cnt = 128 := McLTwo.base.2.2.2.2.1

theorem enum_eq : sylTwoEnum = (hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL).1 := by
  unfold sylTwoEnum
  rw [McLTwo.closure_eq.1]

theorem enum_size : sylTwoEnum.size = 128 := by
  rw [enum_eq, ← cnt_eq]
  simp [hRec]

theorem idx_lt {i : Nat} (hi : i < 6) : wtIdx[i]! < 128 := by
  interval_cases i <;> decide

theorem wtElem_eq {i : Nat} (hi : i < 6) : wtElem i = tabN 275 9 (McLTwoS.T wtIdx[i]!) := by
  have hk : wtIdx[i]! < (hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL).1.size := by
    simpa [hRec, cnt_eq] using idx_lt hi
  unfold wtElem
  rw [enum_eq, getElem!_pos (hRec 275 9 McLTwoS.cnt McLTwoS.T McLTwoS.PL).1 (wtIdx[i]!) hk]
  simp only [hRec, Array.getElem_ofFn]
  rw [tabT_unpack]

theorem gs_getD {j : Nat} (hj : j < 6) (d : Nat) : wtGs.getD j d = McLTwoS.T wtIdx[j]! := by
  simp [wtGs, List.getD_eq_getElem?_getD, hj]

theorem gis_getD {j : Nat} (hj : j < 6) (d : Nat) :
    wtGis.getD j d = invN 275 9 (McLTwoS.T wtIdx[j]!) := by
  simp [wtGis, wtGs, List.getD_eq_getElem?_getD, hj]

theorem letter_eq {z : Int} (hz : z ≠ 0 ∧ z.natAbs ≤ 6) :
    wtLetterT z = tabN 275 9 (if 0 < z then wtGs.getD (z.toNat - 1) (pidn 275 9)
      else wtGis.getD ((-z).toNat - 1) (pidn 275 9)) := by
  have hi : z.natAbs - 1 < 6 := by omega
  unfold wtLetterT
  by_cases h : 0 < z
  · have e : z.toNat - 1 = z.natAbs - 1 := by omega
    rw [if_pos h, if_pos h, wtElem_eq hi, e, gs_getD hi]
  · have e : (-z).toNat - 1 = z.natAbs - 1 := by omega
    rw [if_neg h, if_neg h, wtElem_eq hi, invT_tabN' dims, e, gis_getD hi]

theorem wordT_eq : ∀ wd : List Int, (∀ l ∈ wd, l ≠ 0 ∧ l.natAbs ≤ 6) →
    wordT 275 wtLetterT wd = tabN 275 9 (evalN 275 9 wtGs wtGis wd)
  | [], _ => by
    simp only [wordT, List.foldr_nil, CFSG.KC.Ivk8N.evalN]
    exact idT_tabN' dims
  | l :: wd, h => by
    have ih := wordT_eq wd fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have e : wordT 275 wtLetterT (l :: wd) =
        (wordT 275 wtLetterT wd).map (fun t => (wtLetterT l)[t.toNat]!) := rfl
    rw [e, map_eq_compT' (n := 275) (by rw [ih, size_tabN]), ih,
      letter_eq (h l List.mem_cons_self), compT_tabN' dims, CFSG.KC.Ivk8N.evalN]

theorem rels_letters : ∀ r ∈ wtRels, ∀ l ∈ r.1 ++ r.2, l ≠ 0 ∧ l.natAbs ≤ 6 := by
  decide +kernel

theorem ne_letters : ∀ r ∈ wtNe, ∀ l ∈ r.1 ++ r.2.1, l ≠ 0 ∧ l.natAbs ≤ 6 := by
  decide +kernel

theorem wtCheck_true : wtCheck = true := by
  unfold wtCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine allIn_eq_true.2 fun i _ hi => ?_
    rw [enum_size]
    exact decide_eq_true (idx_lt hi)
  · refine allIn_eq_true.2 fun i _ hi => ?_
    have hk : wtIdx[i]! < sylTwoEnum.size := by
      rw [enum_size]
      exact idx_lt hi
    have h := Array.all_eq_true.1 McLTwo.inv_ok (wtIdx[i]!) hk
    unfold wtElem
    rw [getElem!_pos sylTwoEnum (wtIdx[i]!) hk]
    exact h
  · rw [List.all_eq_true]
    intro r hr
    rw [wordT_eq r.1 fun l hl => rels_letters r hr l (List.mem_append_left _ hl),
      wordT_eq r.2 fun l hl => rels_letters r hr l (List.mem_append_right _ hl), beq_tabN dims]
    exact List.all_eq_true.1 wtRelsN_ok r hr
  · rw [List.all_eq_true]
    intro r hr
    rw [wordT_eq r.1 fun l hl => ne_letters r hr l (List.mem_append_left _ hl),
      wordT_eq r.2.1 fun l hl => ne_letters r hr l (List.mem_append_right _ hl)]
    exact List.all_eq_true.1 wtNeN_ok r hr

end CertificateChecks.KernelIvk8McLWt

end
