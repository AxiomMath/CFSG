module

public import Certificates.Kernel.J4F2.J4M3SixK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2 CertificateChecks.KernelJ4Q CFSG.Quasithin.J4M3

theorem m3_rootV_wf : rootV.wf = true := by decide

theorem m3_wf_get {X : Array V2} (hX : WfA X) (i : Nat) : (X[i]?.getD V2.zero).wf = true := by
  by_cases hi : i < X.size
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some]
    exact Array.all_eq_true.mp hX.2 i hi
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi), Option.getD_none]
    decide

theorem m3_any_range_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    (List.range n).any f = (List.range n).any g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.any_append, List.any_append,
      m3_any_range_congr fun i hi => h i (Nat.lt_succ_of_lt hi), List.any_cons, List.any_cons,
      h n (Nat.lt_succ_self n), List.any_nil, List.any_nil]

theorem m3_rowsDiffer {A B : Array V2} {a b : Nat} (hA : WfA A ∧ encR A = a)
    (hB : WfA B ∧ encR B = b) : rowsDiffer A B = m3Diff a b := by
  unfold rowsDiffer m3Diff
  apply m3_any_range_congr
  intro i hi
  rw [← hA.2, ← hB.2, rowJ_eq (Array.all_eq_true.mp hA.1.2) hi,
    rowJ_eq (Array.all_eq_true.mp hB.1.2) hi]
  exact differs_eq (m3_wf_get hA.1 i) (m3_wf_get hB.1 i)

theorem m3_u5_enc : WfA (u5Rows ()) ∧ encR (u5Rows ()) = m3U :=
  pathM_enc (i := 4) (by norm_num)

theorem m3_u5i_enc : WfA (u5Inv ()) ∧ encR (u5Inv ()) = m3Ui :=
  ⟨(pathMi_enc (i := 4) (by norm_num)).1, (pathMi_enc (i := 4) (by norm_num)).2.1⟩

theorem m3_n_enc : WfA (nRows (locMats ()) (locInvs ())) ∧
    encR (nRows (locMats ()) (locInvs ())) = m3N :=
  mkMul (mkMul (word_enc _) m3_u5_enc) (word_enc _)

theorem m3_ni_enc : WfA (nInvRows (locMats ()) (locInvs ())) ∧
    encR (nInvRows (locMats ()) (locInvs ())) = m3Ni :=
  mkMul (mkMul (word_enc _) m3_u5i_enc) (word_enc _)

theorem m3_pt_enc (m : Nat) :
    (ptVec (nInvRows (locMats ()) (locInvs ())) (uTab (locMats ()) (locInvs ())) m).wf = true ∧
      v2N (ptVec (nInvRows (locMats ()) (locInvs ())) (uTab (locMats ()) (locInvs ())) m) =
        m3Pt m := by
  have hM := mkMul m3_ni_enc (etaU_enc m)
  unfold ptVec eR
  refine ⟨wf_frApply hM.1 rootV, ?_⟩
  rw [v2N_frApply hK hM.1 m3_rootV_wf, hM.2]
  rfl

theorem m3_fixes {P : Array V2} {p : Nat} (hP : WfA P ∧ encR P = p) :
    fixesPts (nInvRows (locMats ()) (locInvs ())) (uTab (locMats ()) (locInvs ())) P =
      m3Fix p := by
  unfold fixesPts m3Fix
  apply mkAll_congr
  intro m _
  rw [beq_v2N, v2N_frApply hK hP.1 (m3_pt_enc m).1, hP.2, (m3_pt_enc m).2]

theorem m3_cent {P : Array V2} {p : Nat} (hP : WfA P ∧ encR P = p) :
    centV0 (uTab (locMats ()) (locInvs ())) P = m3Cent p := by
  unfold centV0 m3Cent eR
  apply mkAll_congr
  intro m _
  exact mkEq (mkMul hP (etaU_enc m)) (mkMul (etaU_enc m) hP)

theorem m3_norm {N Ni : Array V2} {n ni : Nat} (hN : WfA N ∧ encR N = n)
    (hNi : WfA Ni ∧ encR Ni = ni) :
    (v0Gens.all fun c => v0Masks.any fun d =>
      eqRows (mulRows (mulRows N (eR (uTab (locMats ()) (locInvs ())) c)) Ni)
        (eR (uTab (locMats ()) (locInvs ())) d)) = m3Norm n ni := by
  unfold m3Norm eR
  apply mkAll_congr
  intro m _
  congr 1
  funext d
  exact mkEq (mkMul (mkMul hN (etaU_enc m)) hNi) (etaU_enc d)

theorem m3_chkU5 : chkU5 () = true := by
  unfold chkU5
  rw [mkEq (mkMul m3_u5_enc m3_u5i_enc) mkId]
  exact (pathMi_enc (i := 4) (by norm_num)).2.2

theorem m3_chkN : chkN () = true := by
  unfold chkN chkNWith
  simp only []
  rw [m3_norm m3_n_enc m3_ni_enc]
  exact m3_n

theorem m3_pts_eq :
    chkPtsWith (nInvRows (locMats ()) (locInvs ())) (uTab (locMats ()) (locInvs ())) =
      (ptMasks.all (fun m => neN (m3Pt m) (v2N rootV)) &&
        ptMasks.all fun m => ptMasks.all fun d => m == d || neN (m3Pt m) (m3Pt d)) := by
  unfold chkPtsWith
  refine congrArg₂ and ?_ ?_
  · apply mkAll_congr
    intro m _
    rw [differs_eq (m3_pt_enc m).1 m3_rootV_wf, (m3_pt_enc m).2]
  · apply mkAll_congr
    intro m _
    apply mkAll_congr
    intro d _
    rw [differs_eq (m3_pt_enc m).1 (m3_pt_enc d).1, (m3_pt_enc m).2, (m3_pt_enc d).2]

theorem m3_chkPts : chkPts () = true := m3_pts_eq.trans m3_pts

theorem m3_chkP : chkP () = true := by
  unfold chkP chkPWith
  simp only []
  have hX := word_enc xWord
  have hXi := word_enc (invWord xWord)
  have hE : WfA (eR (uTab (locMats ()) (locInvs ())) 1131) ∧
      encR (eR (uTab (locMats ()) (locInvs ())) 1131) = eK 1131 := etaU_enc 1131
  have h1 : ((List.range 12).all fun i =>
      fixesPts (nInvRows (locMats ()) (locInvs ())) (uTab (locMats ()) (locInvs ()))
          (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i) &&
        centV0 (uTab (locMats ()) (locInvs ()))
          (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i)) =
      ((List.range 12).all fun i => m3Fix (pK i) && m3Cent (pK i)) := by
    apply mkRange_congr
    intro i _
    rw [m3_fixes (pK_enc i), m3_cent (pK_enc i)]
  rw [h1, m3_fixes hX, m3_norm hX hXi,
    m3_rowsDiffer (mkMul (mkMul hX hE) hXi) hE]
  exact m3_p

theorem m3_chkQ : chkQ () = true := by
  unfold chkQ chkQWith
  simp only []
  unfold commRows
  have hX := word_enc xWord
  have hXi := word_enc (invWord xWord)
  have e : ∀ i, WfA (mulRows (mulRows (mulRows
        (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i)
        (wordRows (locMats ()) (locInvs ()) xWord))
        (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i))
        (wordRows (locMats ()) (locInvs ()) (invWord xWord))) ∧
      encR (mulRows (mulRows (mulRows
        (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i)
        (wordRows (locMats ()) (locInvs ()) xWord))
        (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i))
        (wordRows (locMats ()) (locInvs ()) (invWord xWord))) =
        commK (pK i) (wK xWord) (piK i) (wK (invWord xWord)) :=
    fun i => mkMul (mkMul (mkMul (pK_enc i) hX) (piK_enc i)) hXi
  have e' : ∀ i, WfA (mulRows (mulRows (mulRows
        (wordRows (locMats ()) (locInvs ()) xWord)
        (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i))
        (wordRows (locMats ()) (locInvs ()) (invWord xWord)))
        (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i)) ∧
      encR (mulRows (mulRows (mulRows
        (wordRows (locMats ()) (locInvs ()) xWord)
        (pRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i))
        (wordRows (locMats ()) (locInvs ()) (invWord xWord)))
        (pInvRows (locMats ()) (locInvs ()) (uTab (locMats ()) (locInvs ())) i)) =
        commK (wK xWord) (pK i) (wK (invWord xWord)) (piK i) :=
    fun i => mkMul (mkMul (mkMul hX (pK_enc i)) hXi) (piK_enc i)
  refine Eq.trans ?_ m3_q
  apply mkRange_congr
  intro i _
  unfold eR
  rw [mkEq (mkMul (e i) (e i)) (etaU_enc _)]
  congr 1
  apply mkRange_congr
  intro j _
  exact mkEq (mkMul (mkMul (mkMul (e i) (e j)) (e' i)) (e' j)) (etaU_enc _)

theorem m3_chkC : chkC () = true := by
  unfold chkC chkCWith
  simp only []
  have hC := word_enc cWord
  rw [m3_cent hC, beq_v2N, beq_v2N, beq_v2N, beq_v2N,
    v2N_frApply hK hC.1 (m3_pt_enc 0).1, v2N_frApply hK hC.1 (m3_pt_enc 1).1,
    v2N_frApply hK hC.1 (m3_pt_enc 16).1, v2N_frApply hK hC.1 (m3_pt_enc 17).1, hC.2,
    (m3_pt_enc 0).2, (m3_pt_enc 1).2, (m3_pt_enc 16).2, (m3_pt_enc 17).2]
  exact m3_c

open CFSG.Quasithin.J4M3 in
theorem c7245 : (chkU5 () = true) ∧ (chkN () = true) ∧ (chkPts () = true) ∧ (chkP () = true) ∧
    (chkQ () = true) ∧ (chkC () = true) :=
  ⟨m3_chkU5, m3_chkN, m3_chkPts, m3_chkP, m3_chkQ, m3_chkC⟩

end CertificateChecks.KernelJ4F2

end
