module

public import Certificates.Kernel.SmithL6K.GlueO
public import Certificates.Kernel.SmithL6K.ChecksR
public import Certificates.Kernel.SmithL6Coll.Assemble
public import CFSG.Certificates.Kernel.SmithL6KRSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel CFSG.SmithL6.CollK
open CFSG.SmithE (applyCols)

theorem trL_facts : trL = KernelSmithL6Coll.rtop.flatten ∧ trL.length = 651 ∧
    ∀ A ∈ trL, A.length = 9 := by
  have h := trL_ok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem trL_collL : collL = (trL.map List.toArray).toArray := by
  rw [collL_eq KernelSmithL6Coll.rtop KernelSmithL6Coll.rtop_length KernelSmithL6Coll.topAll,
    ← trL_facts.1]

theorem collL_size : collL.size = 651 := by
  rw [trL_collL, List.size_toArray, List.length_map, trL_facts.2.1]

theorem collL_get {v : Nat} (hv : v < 651) : collL[v]! = (trL.getD v []).toArray := by
  have hl : v < trL.length := by rw [trL_facts.2.1]; exact hv
  rw [trL_collL, getElem!_pos _ v (by rw [List.size_toArray, List.length_map]; exact hl),
    List.getElem_toArray, List.getElem_map, getD_of_lt hl]

theorem trL_len {v : Nat} (hv : v < 651) : (trL.getD v []).length = 9 := by
  have hl : v < trL.length := by rw [trL_facts.2.1]; exact hv
  rw [getD_of_lt hl]
  exact trL_facts.2.2 _ (List.getElem_mem hl)

theorem trGens_size : trGens.size = 6 := by decide

theorem trGens_get {g : Nat} (hg : g < 6) :
    trGens[g]! = trGens.toList[g]'(by rw [Array.length_toList, trGens_size]; exact hg) := by
  rw [getElem!_pos trGens g (by rw [trGens_size]; exact hg), Array.getElem_toList]

theorem trGens_facts : (∀ g < 6, trGens[g]! < 1953 ∧ planeImg trGens[g]! 0 = 0) ∧
    (∀ g < 6, (trGens.map ucols)[g]! = (trG.getD g []).toArray) ∧
    ∀ g < 6, (trG.getD g []).length = 9 := by
  have h := trG_ok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hfix, hmap⟩, hlen⟩ := h
  have hl : trGens.toList.length = 6 := by rw [Array.length_toList, trGens_size]
  have hm : ∀ g < 6, trGens[g]! ∈ trGens.toList := fun g hg => by
    rw [trGens_get hg]
    exact List.getElem_mem _
  have hGl : trG.length = 6 := by rw [← hmap, List.length_map, hl]
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨hp, e⟩ := hfix _ (hm g hg)
    refine ⟨hp, planeImg_wt hp (by decide) (by decide) ?_⟩
    rw [← tvCols_eq hp, wtP_eq (by decide), ← applyCols_toArray, Array.toArray_toList] at e
    exact e.symm
  · have hp := (hfix _ (hm g hg)).1
    rw [getElem!_pos _ g (by rw [Array.size_map, trGens_size]; exact hg), Array.getElem_map,
      ← getElem!_pos trGens g (by rw [trGens_size]; exact hg), ucols_eq hC hI p0_planePts hp,
      ← hmap, getD_of_lt (by rw [List.length_map, hl]; exact hg), List.getElem_map, trGens_get hg]
  · have h : g < trG.length := by rw [hGl]; exact hg
    rw [getD_of_lt h]
    exact hlen _ (List.getElem_mem h)

theorem tvImgP_lt {j : Nat} (hj : j < 1953) {x : Nat} (hx : x < 1953) :
    tvImgP tcP idxP j x = tvImg j x := tvImgP_tvImg hj hx

@[expose] def liftF : Nat → Nat → Nat
  | 0 => id
  | 1 => tvImg 0
  | 2 => tvImg 224
  | 3 => fun x => tvImg 0 (tvImg 224 x)
  | _ => fun k => trTauT[k]!

theorem liftF_table : ∀ {j : Nat}, j < 5 → ∀ x < 1953, (trLift j)[x]! = liftF j x
  | 0, _, _, hx => ofFn_get! (fun x : Fin 1953 => x.val) hx
  | 1, _, _, hx => tvTab_get (by decide) hx
  | 2, _, _, hx => tvTab_get (by decide) hx
  | 3, _, x, hx => by
    change (trCompT (trTvT 0) (trTvT 224))[x]! = tvImg 0 (tvImg 224 x)
    unfold trCompT trTvT
    rw [ofFn_get! _ hx]
    change (tvTab[0]!)[(tvTab[224]!)[x]!]! = _
    rw [tvTab_get (by decide) hx, tvTab_get (by decide) (tvImg_lt (by decide) hx)]
  | 4, _, _, _ => rfl
  | _ + 5, h, _, _ => absurd h (by omega)

theorem trLift_checks : (tvImgP tcP idxP 0 224 = 224 ∧ fixW0K p0 (tvImgP tcP idxP 0) = true ∧
    fixW0K p0 (tvImgP tcP idxP 224) = true ∧
    fixW0K p0 (fun x => tvImgP tcP idxP 0 (tvImgP tcP idxP 224 x)) = true ∧
    fixW0K p0 (tauP tcP idxP) = true) ∧
    trR = [colsF p0 (tvImgP tcP idxP 0), colsF p0 (tvImgP tcP idxP 224),
      colsF p0 (fun x => tvImgP tcP idxP 0 (tvImgP tcP idxP 224 x)), colsF p0 (tauP tcP idxP)] := by
  have h := trLift_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩, h.2⟩

theorem liftF_lift : ∀ {j : Nat}, j < 5 → LiftF (liftF j)
  | 0, _ => liftF_id
  | 1, _ => liftF_tvImg (by decide)
  | 2, _ => liftF_tvImg (by decide)
  | 3, _ => liftF_comp (f := tvImg 0) (g := tvImg 224) (liftF_tvImg (by decide))
      (liftF_tvImg (by decide)) fun x hx => by
    rw [tvImg_comp (j := 0) (a := 224) (by decide) (by decide) hx,
      ← tvImgP_lt (j := 0) (x := 224) (by decide) (by decide), trLift_checks.1.1]
  | 4, _ => liftF_tau
  | _ + 5, h => absurd h (by omega)

@[expose] noncomputable def liftP : Nat → Nat → Nat
  | 1 => tvImgP tcP idxP 0
  | 2 => tvImgP tcP idxP 224
  | 3 => fun x => tvImgP tcP idxP 0 (tvImgP tcP idxP 224 x)
  | _ => tauP tcP idxP

theorem liftP_eq : ∀ {j : Nat}, j < 5 → 0 < j → ∀ x < 1953, liftF j x = liftP j x
  | 1, _, _, _, hx => (tvImgP_lt (by decide) hx).symm
  | 2, _, _, _, hx => (tvImgP_lt (by decide) hx).symm
  | 3, _, _, x, hx => by
    change tvImg 0 (tvImg 224 x) = tvImgP tcP idxP 0 (tvImgP tcP idxP 224 x)
    rw [tvImgP_lt (by decide) hx, tvImgP_lt (by decide) (tvImg_lt (by decide) hx)]
  | 4, _, _, _, hx => (tauP_eq hC hI hx).symm
  | 0, _, h, _, _ => absurd h (by omega)
  | _ + 5, h, _, _, _ => absurd h (by omega)

theorem liftP_W0 : ∀ {j : Nat}, j < 5 → 0 < j → fixW0K p0 (liftP j) = true
  | 1, _, _ => trLift_checks.1.2.1
  | 2, _, _ => trLift_checks.1.2.2.1
  | 3, _, _ => trLift_checks.1.2.2.2.1
  | 4, _, _ => trLift_checks.1.2.2.2.2
  | 0, _, h => absurd h (by omega)
  | _ + 5, h, _ => absurd h (by omega)

theorem liftF_W0 {j : Nat} (hj : j < 5) :
    ∀ p ∈ planePtsArr[0]!, (flagArr[0]!)[(trLift j)[p]!]! = true := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · intro p hp
    rw [planePtsArr_get (by decide), p0_planePts, List.mem_toArray] at hp
    obtain ⟨hp1, hp2⟩ := mem_planePts0 p0_planePts hp
    rw [liftF_table (j := 0) (by decide) p hp1]
    change (flagArr[0]!)[p]! = true
    rw [flagArr_get (j := 0) (by decide) hp1]
    exact hp2
  · exact lift_W0 p0_planePts (fun x hx => by rw [liftF_table hj x hx, liftP_eq hj hj0 x hx])
      (liftP_W0 hj hj0)

theorem trLift_facts : ∀ j < 5,
    (∀ x < 1953, (trLift j)[x]! < 1953 ∧ (trLift j)[(trLift j)[x]!]! = x) ∧
    (∀ p < 1953, ∀ x < 1953,
      (trLift j)[(tvTab[p]!)[x]!]! = (tvTab[(trLift j)[p]!]!)[(trLift j)[x]!]!) ∧
    ∀ p ∈ planePtsArr[0]!, (flagArr[0]!)[(trLift j)[p]!]! = true := fun j hj =>
  ⟨(lift_facts (liftF_table hj) (liftF_lift hj)).1,
    (lift_facts (liftF_table hj) (liftF_lift hj)).2, liftF_W0 hj⟩

theorem rootMat_eq {j : Nat} (hj : j < 5) (hj0 : 0 < j) :
    trColsT (trLift j) = (colsF p0 (liftP j)).toArray := by
  rw [trColsT_eq p0_planePts fun k hk => liftF_table hj _ (ugens_lt k hk)]
  exact congrArg List.toArray (colsF_congr fun k hk => liftP_eq hj hj0 _ (ugens_lt k hk))

theorem trRootMats_eq : trRootMats () = trR.map List.toArray := by
  have e : trRootMats () =
      [trColsT (trLift 1), trColsT (trLift 2), trColsT (trLift 3), trColsT (trLift 4)] := rfl
  rw [e, trLift_checks.2, rootMat_eq (j := 1) (by decide) (by decide),
    rootMat_eq (j := 2) (by decide) (by decide), rootMat_eq (j := 3) (by decide) (by decide),
    rootMat_eq (j := 4) (by decide) (by decide)]
  rfl

theorem tr_reach : Reach 651 6 (fun v => (trRootMats ()).any fun A => A == collL[v]!)
    (fun g u v => trConjC (trGens.map ucols)[g]! collL[v]! == collL[u]!) := by
  refine ((reach_of_treeK trTree_ok).roots fun v hv hr => ?_).mono
    fun g hg u hu v hv he => ⟨g, hg, ?_⟩
  · rw [trRootMats_eq, collL_get hv, List.any_map]
    unfold rootK at hr
    simpa only [Function.comp_def, toArray_beq] using hr
  · obtain ⟨-, hG, hGl⟩ := trGens_facts
    rw [hG g hg, collL_get hv, collL_get hu, trConjC_toArray _ _ (hGl g hg) (trL_len hv),
      toArray_beq]
    exact he

end CertificateChecks.KernelSmithL6K
