module

public import Certificates.Kernel.SmithL6K.GluePr
public import Certificates.Data.SmithL6TrDist

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel

theorem img_invol {s : Nat} (hs : s < gns.length) {j : Nat} (hj : j < 1395) :
    fldW 11 (gpP.getD s 0) (fldW 11 (gpP.getD s 0) j) = j := by
  have hg := gns_lt s hs
  have hj0 := (row_facts s hs j hj).1
  refine wt_inj _ (row_facts s hs _ hj0).1 _ hj ?_
  rw [(row_facts s hs _ hj0).2.1, (row_facts s hs j hj).2.1, tvCols_invol hg _ (wt_lt20K j)]

theorem img_meet {s : Nat} (hs : s < gns.length) {u j : Nat} (hu : u < 1395) (hj : j < 1395) :
    (setM (wMask (fldW 11 (gpP.getD s 0) u)) ∩ setM (wMask (fldW 11 (gpP.getD s 0) j))).card =
      (setM (wMask u) ∩ setM (wMask j)).card := by
  have hg := gns_lt s hs
  rw [(row_facts s hs u hu).2.2, (row_facts s hs j hj).2.2,
    ← Finset.image_inter _ _ (tvApply_inj hg), Finset.card_image_of_injective _ (tvApply_inj hg)]

@[expose] noncomputable def meet2 (i : Nat) : Nat :=
  ((Finset.range 1395).filter fun j => (setM (wMask i) ∩ setM (wMask j)).card = 2).card

theorem card_meet2_step {s : Nat} (hs : s < gns.length) {u : Nat} (hu : u < 1395) :
    meet2 (fldW 11 (gpP.getD s 0) u) = meet2 u := by
  unfold meet2
  refine Finset.card_nbij' (fun j => fldW 11 (gpP.getD s 0) j)
    (fun j => fldW 11 (gpP.getD s 0) j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj ⊢
    have hj0 := (row_facts s hs j hj.1).1
    refine ⟨hj0, ?_⟩
    rw [← img_meet hs hu hj0, img_invol hs hj.1]
    exact hj.2
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨(row_facts s hs j hj.1).1, ?_⟩
    rw [img_meet hs hu hj.1]
    exact hj.2
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    exact img_invol hs hj.1
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    exact img_invol hs hj.1

theorem countP_twoB {i : Nat} (hi : i < 1395) :
    ((List.range 1395).countP fun j => twoB (wMask i &&& wMask j)) = meet2 i := by
  rw [← card_filter_range]
  unfold meet2
  refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  obtain ⟨hx, hX, h8⟩ := inter_facts hi hj'
  rw [twoB_iff hx hX h8, setM_and]

theorem meet2_zero : meet2 0 = 784 := by
  have h := dist2_row0
  unfold dist2K at h
  have hl0 : 0 < wmk.length := by rw [wmk_length]; decide
  have hm : wmk.getD 0 0 ∈ wmk.take 1 := by
    have e := List.getElem_mem (l := wmk.take 1) (n := 0) (by rw [List.length_take]; omega)
    rw [List.getElem_take] at e
    rw [getD_of_lt hl0]
    exact e
  have h := beq_iff_eq.mp (List.all_eq_true.mp h _ hm)
  have hl : wmk = (List.range 1395).map fun j => wmk.getD j 0 := by
    refine List.ext_getElem (by rw [List.length_map, List.length_range, wmk_length]) ?_
    intro n h1 h2
    rw [List.getElem_map, List.getElem_range, getD_of_lt h1]
  rw [← wMask_eq (by decide)] at h
  rw [hl, List.countP_map] at h
  rw [← countP_twoB (by decide), ← h]
  refine List.countP_congr fun j hj => ?_
  rw [wMask_eq (List.mem_range.mp hj), Function.comp_apply]

theorem meet2_all : ∀ i < 1395, meet2 i = 784 := by
  refine reach_planes (fun i => meet2 i = 784) (fun v _ hv => by
    rw [beq_iff_eq.mp hv]
    exact meet2_zero) ?_
  intro s hs u hu v _ he hQ
  rw [← beq_iff_eq.mp he, card_meet2_step hs hu]
  exact hQ

theorem trChkDist2_holds : trChkDist2 = true := by
  unfold trChkDist2
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [beq_iff_eq, ← List.countP_eq_length_filter, ← meet2_all i hi', ← countP_twoB hi']
  refine List.countP_congr fun j hj => ?_
  rw [meetCard_one_iff hi' (List.mem_range.mp hj)]

end CertificateChecks.KernelSmithL6K
