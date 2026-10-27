module

public import Certificates.Kernel.L52Insp443.NGlue
public import Certificates.Kernel.L52Insp443.CentGlue

public section

set_option maxRecDepth 20000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Sporadic.Schreier.Native

theorem getD_map_lt {α β : Type} (l : List α) (f : α → β) {j : ℕ} (hj : j < l.length) (d : β)
    (d' : α) : (l.map f).getD j d = f (l.getD j d') := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
    List.getD_eq_getElem _ _ hj]

theorem w_facts {w : ℕ} (hw : ch725109w w = true) :
    (D.aB.getD w []).getD 0 [] = D.a0B.getD w [] ∧ (D.aB.getD w []).getD 1 [] = D.a1B.getD w [] ∧
      (D.aB.getD w []).getD 2 [] = List.zipWith mmulK (D.a0B.getD w []) (D.a1B.getD w []) ∧
      (D.aB.getD w []).length = 3 ∧ (D.aS.getD w []).length = 3 ∧
      ∀ i < 3, spanK ((D.aB.getD w []).getD i []) = (D.aS.getD w []).getD i [] := by
  obtain ⟨-, r⟩ := and2 hw
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨c3, r⟩ := and2 r
  obtain ⟨c4, r⟩ := and2 r
  obtain ⟨c5, r⟩ := and2 r
  obtain ⟨c6, r⟩ := and2 r
  obtain ⟨c7, r⟩ := and2 r
  obtain ⟨c8, -⟩ := and2 r
  exact ⟨(listBeq_iff _ _).mp c3, (listBeq_iff _ _).mp c4, (listBeq_iff _ _).mp c5,
    Nat.eq_of_beq_eq_true c6, Nat.eq_of_beq_eq_true c7,
    fun i hi => (listBeq_iff _ _).mp ((allK_iff _ _).mp c8 i (List.mem_range.mpr hi))⟩

theorem tabs_aB {w : ℕ} (hw : ch725109w w = true) (hu : ch725109u w = true) {i : ℕ}
    (hi : i < 3) :
    List.Forall₂ (Rep 31) ((aB w).getD i [])
        (((D.aB.getD w []).getD i []).map fun u => glPerm (gD u)) ∧
      ∀ c ∈ (D.aB.getD w []).getD i [], unitK c = true := by
  obtain ⟨c3, c4, c5, -⟩ := w_facts hw
  obtain ⟨u0, u1⟩ := and2 hu
  have h0 := forall₂_of_tabsK u0
  have h1 := forall₂_of_tabsK u1
  rw [aB.eq_1]
  interval_cases i
  · rw [List.getD_cons_zero, c3]
    exact h0
  · rw [List.getD_cons_succ, List.getD_cons_zero, c4]
    exact h1
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, c5, diagT.eq_1]
    exact forall₂_zip h0.1 h0.2 h1.1 h1.2

@[expose] noncomputable def sumA (w i : ℕ) : Subgroup G := subK ((D.aB.getD w []).getD i [])

theorem perm_of {w : ℕ} (hw : ch725109w w = true) (hu : ch725109u w = true) (y : G)
    (hy : permP (D.aB.getD w []) (D.aS.getD w []) (mcode (y : Mat)) (mcode ((y⁻¹ : G) : Mat)) =
      true) : y ∈ permSub (sumA w) 3 := by
  obtain ⟨-, -, -, h6, h7, h8⟩ := w_facts hw
  intro i hi
  have hmem : (D.aB.getD w []).getD i [] ∈ D.aB.getD w [] := by
    rw [List.getD_eq_getElem (D.aB.getD w []) [] (by rw [h6]; exact hi)]
    exact List.getElem_mem _
  obtain ⟨S, hS, hn⟩ := (anyK_iff _ _).mp ((allK_iff _ _).mp hy _ hmem)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hS
  have hj3 : j < 3 := by rw [← h7]; exact hj
  refine ⟨j, hj3, fun x hx => ?_⟩
  rw [← List.getD_eq_getElem _ [] hj, ← h8 j hj3] at hn
  have hc := normP_conj (tabs_aB hw hu hi).2 hn
  exact conj_mem_of_gens (fun b hb => mem_subK_of_code (tabs_aB hw hu hj3).2 (hc b hb)) hx

theorem perm3Of {w : ℕ} (hw : ch725109w w = true)
    (hu : ch725109u w = true) (hp : ch725109p w = true) (hf : ch725109f w = true)
    (hac : ∀ i < 3, clK ((D.aB.getD w []).getD i []) ((D.aS.getD w []).getD i []) = true)
    (hm : 0 < (D.oW.getD w []).length) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    perm3TestS 31 (wB w) (spanTabs 31 (wB w)) (aB w) ((aB w).map (spanTabs 31)) T = false := by
  obtain ⟨-, -, -, -, -, h8⟩ := w_facts hw
  obtain ⟨hWT, hWu⟩ := forall₂_of_tabsK (tabs_wB hu)
  rw [← Bool.not_eq_true]
  intro hP
  unfold perm3TestS at hP
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hP
  obtain ⟨hn, hall⟩ := hP
  have hN := normalizer_of_conj_glPerm hWu ((conjIn_iff_codes hWT hWT hWu hT).mp hn)
  have hS := normalizer_le_stabK hWu hN
  have hp' : orbOK (List.append (D.a0B.getD w []) (D.a1B.getD w [])) (D.oW.getD w [])
      (permP (D.aB.getD w []) (D.aS.getD w [])) (mcode ((glA : G) : Mat))
      (mcode ((glA⁻¹ : G) : Mat)) (mcode ((glB : G) : Mat)) (mcode ((glB⁻¹ : G) : Mat)) = true := by
    rw [gis_code (by norm_num) gsA, gis_code (by norm_num) gsB, gsA, gsB]
    exact hp
  have hQ := (orb_sound closure_glAB hm hp' (recU hf) (permSub (sumA w) 3) (perm_of hw hu)).2 hS
  have hlen : (aB w).length = 3 := by
    rw [aB.eq_1]
    rfl
  rw [← Bool.not_eq_true] at hall
  apply hall
  rw [List.all_eq_true]
  intro i hi
  have hi3 := List.mem_range.mp hi
  obtain ⟨j, hj3, hx⟩ := hQ i hi3
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hj3, ?_⟩
  rw [getD_map_lt _ _ (by rw [hlen]; exact hj3) [] []]
  obtain ⟨hAi, hui⟩ := tabs_aB hw hu hi3
  obtain ⟨hAj, huj⟩ := tabs_aB hw hu hj3
  obtain ⟨hcl, hsq⟩ := cl_facts (hac j hj3)
  rw [← h8 j hj3] at hcl
  refine (conjIn_iff_codes hAi hAj huj hT).mpr fun u hu' => ⟨h * gD u * h⁻¹, ?_, ?_⟩
  · exact mem_spanK_of_subK huj hcl hsq (hx _ (gD_mem_subK hu'))
  · rw [← map_mul, ← map_mul, inv_mul_cancel_right]

theorem e64_perm3Test {w : ℕ} (hw : w < 2) (h : G) {T : Table}
    (hT : Rep 31 T (glPerm h)) :
    perm3TestS 31 (wB w) (spanTabs 31 (wB w)) (aB w) ((aB w).map (spanTabs 31)) T = false := by
  have hl : 0 < (D.oW.getD w []).length := by
    interval_cases w <;> decide +kernel
  interval_cases w
  · refine perm3Of ch725109w0 ch725109u0 ch725109p0 ch725109f0 (fun i hi => ?_) hl h hT
    interval_cases i
    · exact ch725109ac0
    · exact ch725109ac1
    · exact ch725109ac2
  · refine perm3Of ch725109w1 ch725109u1 ch725109p1 ch725109f1 (fun i hi => ?_) hl h hT
    interval_cases i
    · exact ch725109ac3
    · exact ch725109ac4
    · exact ch725109ac5

end CertificateChecks.KernelL52I

end
