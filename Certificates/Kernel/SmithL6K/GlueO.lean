module

public import Certificates.Kernel.SmithL6K.GluePr
public import Certificates.Kernel.SmithL6K.GlueT
public import Certificates.Kernel.SmithL6K.ChecksO
public import CFSG.Certificates.Kernel.SmithL6KOSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel CFSG.SmithL6.CollK
open CFSG.SmithE (applyCols)

theorem planeImg_wt {k u v : Nat} (hk : k < 1953) (hu : u < 1395) (hv : v < 1395)
    (h : wt v = applyCols (tvCols k) (wt u)) : planeImg k u = v :=
  planeImg_of_wt tw_holds wt_inj hk hu hv h

theorem trans_reach : Reach 1395 1953 (· == 0) (fun k u v => planeImg k u == v) := by
  refine Reach.mono reach_planes fun s hs u hu v hv he => ⟨gns.getD s 0, gns_lt s hs, ?_⟩
  obtain ⟨-, hw, -⟩ := row_facts s hs u hu
  rw [beq_iff_eq.mp he] at hw
  exact beq_iff_eq.mpr (planeImg_wt (gns_lt s hs) hu hv hw)

theorem meetK_eq {j : Nat} (hj : j < 1395) : meetK wmP j = meetCard 0 j := by
  rw [meetCard_formula_countP (by decide) hj]
  unfold meetK
  rw [wmP_eq (by decide), wmP_eq hj]

theorem dRoot_eq (c : Nat) : dRoot c = dRootK wmP c := by
  unfold dRoot dRootK
  rw [find?_congr (q := fun j => meetK wmP j == c) fun j hj => by
    rw [meetK_eq (List.mem_range.mp hj)]]

theorem sgn_facts : ∀ s < sgn.length, sgn.getD s 0 < 1953 ∧ planeImg (sgn.getD s 0) 0 = 0 ∧
    (tvCols (sgn.getD s 0)).toList = sgc.getD s [] := by
  intro s hs
  have h := sgn_ok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hlt, hmap⟩, hfix⟩ := h
  have hp : sgn.getD s 0 < 1953 := by
    rw [getD_of_lt hs]
    exact hlt _ (List.getElem_mem hs)
  have key : ∀ (L : List Nat) (M : List (List Nat)), L.map (fun p => tcl.getD p []) = M →
      s < L.length → M.length = L.length ∧ M.getD s [] = tcl.getD (L.getD s 0) [] := by
    intro L M e hL
    subst e
    refine ⟨List.length_map .., ?_⟩
    rw [getD_of_lt (by rw [List.length_map]; exact hL), List.getElem_map, getD_of_lt hL]
  obtain ⟨hlen, hget⟩ := key sgn sgc hmap hs
  have hs' : s < sgc.length := by rw [hlen]; exact hs
  have hc : (tvCols (sgn.getD s 0)).toList = sgc.getD s [] := by
    rw [tvCols_eq hp, hget]
  refine ⟨hp, planeImg_wt hp (by decide) (by decide) ?_, hc⟩
  have e := hfix _ (List.getElem_mem hs')
  rw [← getD_of_lt (d := []) hs', ← hc, wtP_eq (by decide)] at e
  rw [← applyCols_toArray, Array.toArray_toList] at e
  exact e.symm

theorem plane_reach : Reach 1395 1953 (fun j => j == dRoot (meetCard 0 j))
    (fun p u v => planeImg p 0 == 0 && meetCard 0 u == meetCard 0 v && planeImg p u == v) := by
  refine ((reach_of_treeK otr_ok).roots fun v hv hr => ?_).mono
    fun s hs u hu v hv he => ⟨sgn.getD s 0, (sgn_facts s hs).1, ?_⟩
  · rw [← meetK_eq hv, dRoot_eq]
    exact hr
  · obtain ⟨hp, h0, hc⟩ := sgn_facts s hs
    unfold oEdgeK at he
    simp only [Bool.and_eq_true, beq_iff_eq] at he ⊢
    obtain ⟨hw, hm⟩ := he
    rw [meetK_eq hu, meetK_eq hv] at hm
    refine ⟨⟨h0, hm⟩, planeImg_wt hp hu hv ?_⟩
    rw [← wtP_eq hv, hw, ← hc, ← applyCols_toArray, Array.toArray_toList, wtP_eq hu]

theorem p0_planePts : planePts 0 = p0.toArray := by
  unfold planePts
  rw [← p0_ok]
  unfold p0K
  refine congrArg List.toArray (List.filter_congr fun a ha => ?_)
  have ha' := List.mem_range.mp ha
  have hpa := tvP_tvPair ha'
  simp only [inPlane]
  rw [maskArr_get (by decide), annArr_eq (by decide), wMask_eq (by decide), fld_tcP ha',
    codeOf_div hpa, codeOf_mod hpa]

theorem sgu_get {s : Nat} (hs : s < sgn.length) :
    sgu.getD s [] = ucolsK tcP idxP p0 (sgn.getD s 0) := by
  rw [← sgu_ok, getD_of_lt (by rw [List.length_map]; exact hs), List.getElem_map,
    getD_of_lt hs]

theorem u_reach : Reach 512 1953 (fun v => v == uRoot uSums (uCls uSums v))
    (fun p u v => planeImg p 0 == 0 && uCls uSums u == uCls uSums v &&
      applyCols (ucols p) u == v) := by
  refine ((reach_of_treeK utr_ok).roots fun v hv hr => ?_).mono
    fun s hs u hu v hv he => ⟨sgn.getD s 0, (sgn_facts s hs).1, ?_⟩
  · rw [uCls_eq s2a_ok s2b_ok hv, uRoot_eq s2a_ok s2b_ok]
    exact hr
  · obtain ⟨hp, h0, -⟩ := sgn_facts s hs
    unfold uEdgeK at he
    simp only [Bool.and_eq_true, beq_iff_eq] at he ⊢
    obtain ⟨hc, ha⟩ := he
    refine ⟨⟨h0, by rw [uCls_eq s2a_ok s2b_ok hu, uCls_eq s2a_ok s2b_ok hv]; exact hc⟩, ?_⟩
    rw [ucols_eq hC hI p0_planePts hp, applyCols_toArray, ← sgu_get hs]
    exact ha

theorem u_counts : (List.range 512).countP (fun v => uCls uSums v == 1) = 49 ∧
    (List.range 512).countP (fun v => uCls uSums v == 2) = 294 ∧
    (List.range 512).countP (fun v => uCls uSums v == 3) = 168 := by
  have e : ∀ c, (List.range 512).countP (fun v => uCls uSums v == c) =
      (List.range 512).countP (fun v => uClsK s2m v == c) := fun c =>
    List.countP_congr fun v hv => by rw [uCls_eq s2a_ok s2b_ok (List.mem_range.mp hv)]
  have h := ucnt_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [e, e, e]
  exact ⟨h.1.1, h.1.2, h.2⟩

end CertificateChecks.KernelSmithL6K
