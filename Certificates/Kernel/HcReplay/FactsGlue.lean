module

public import Certificates.Kernel.HcReplay.Facts
public import Certificates.Kernel.HcReplay.SubsGlue
import all Certificates.Data.Kernel.HcPack
import all Certificates.Data.G23RecogGlueInputs
public import Certificates.Data.G23RecogHFactsInputs
import all Certificates.Data.G23RecogHFactsInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData

theorem VL_Lx (u : ↥Hc) : VL (Lx u) := VL_Lst _

theorem mulL_eq_iff {a b c d : List ℕ} (ha : VL a) (hb : VL b) (hc : VL c) (hd : VL d) :
    mulL a b = mulL c d ↔ mulP (pk a) (pk b) = mulP (pk c) (pk d) := by
  rw [← pk_mulL ha hb, ← pk_mulL hc hd]
  exact ⟨congrArg pk, VL_inj (VL_mulL ha hb) (VL_mulL hc hd)⟩

theorem pk_mem_elts {l : List ℕ} (hl : l ∈ elts) : pk l ∈ hcElts.E := by
  rw [← elts_map_pk_eq]
  exact List.mem_map_of_mem hl

theorem pk_mem_of {L : List (List ℕ)} {C : List ℕ} (hC : L.map pk = C) {l : List ℕ} (hl : l ∈ L) :
    pk l ∈ C := by
  rw [← hC]
  exact List.mem_map_of_mem hl

theorem mem_cl_of {ss : List ↥Hc} {C : List ℕ} (hC : (cl ss).map pk = C) {l : List ℕ} (hl : VL l)
    (h : pk l ∈ C) : l ∈ cl ss := by
  rw [mem_iff_pk (VL_cl ss) hl, hC]
  exact h

theorem pk_Lx_mem {ss : List ↥Hc} {S : List ℕ} (hS : (ss.map Lx).map pk = S) {s : ↥Hc}
    (hs : s ∈ ss) : pk (Lx s) ∈ S :=
  pk_mem_of hS (List.mem_map_of_mem hs)

theorem exists_of_pk_mem {ss : List ↥Hc} {C : List ℕ} (hC : (cl ss).map pk = C) {c : ℕ}
    (h : c ∈ C) : ∃ l ∈ cl ss, pk l = c := by
  rw [← hC] at h
  exact List.mem_map.1 h

variable {u v : ↥Hc} {ss sA : List ↥Hc} {cu cv cvi : ℕ} {A C S Ps : List ℕ}

theorem centOK_of (hu : pk (Lx u) = cu) (hC : (cl ss).map pk = C) (hS : (ss.map Lx).map pk = S)
    (h1 : ∀ c ∈ hcElts.E, mulP cu c = mulP c cu → c ∈ C) (h2 : ∀ s ∈ S, mulP cu s = mulP s cu) :
    CentOK u ss := by
  refine ⟨fun l hl hc => ?_, fun s hs => ?_⟩
  · have hv := VL_elts l hl
    refine mem_cl_of hC hv (h1 _ (pk_mem_elts hl) ?_)
    rw [← hu]
    exact (mulL_eq_iff (VL_Lx u) hv hv (VL_Lx u)).1 hc
  · rw [mulL_eq_iff (VL_Lx u) (VL_Lx s) (VL_Lx s) (VL_Lx u), hu]
    exact h2 _ (pk_Lx_mem hS hs)

theorem cent2OK_of (hu : pk (Lx u) = cu) (hv : pk (Lx v) = cv) (hC : (cl ss).map pk = C)
    (hS : (ss.map Lx).map pk = S)
    (h1 : ∀ c ∈ hcElts.E, mulP cu c = mulP c cu → mulP cv c = mulP c cv → c ∈ C)
    (h2 : ∀ s ∈ S, mulP cu s = mulP s cu ∧ mulP cv s = mulP s cv) : Cent2OK u v ss := by
  refine ⟨fun l hl hc hc' => ?_, fun s hs => ?_⟩
  · have hl' := VL_elts l hl
    refine mem_cl_of hC hl' (h1 _ (pk_mem_elts hl) ?_ ?_)
    · rw [← hu]
      exact (mulL_eq_iff (VL_Lx u) hl' hl' (VL_Lx u)).1 hc
    · rw [← hv]
      exact (mulL_eq_iff (VL_Lx v) hl' hl' (VL_Lx v)).1 hc'
  · rw [mulL_eq_iff (VL_Lx u) (VL_Lx s) (VL_Lx s) (VL_Lx u),
      mulL_eq_iff (VL_Lx v) (VL_Lx s) (VL_Lx s) (VL_Lx v), hu, hv]
    exact h2 _ (pk_Lx_mem hS hs)

theorem normSetOK_of (hA : (cl sA).map pk = A) (hP : (sA.map Lx).map pk = Ps)
    (hC : (cl ss).map pk = C) (hS : (ss.map Lx).map pk = S)
    (h1 : ∀ c ∈ hcElts.E, (∀ p ∈ Ps, ∃ d ∈ A, mulP c p = mulP d c) → c ∈ C)
    (h2 : ∀ s ∈ S, ∀ p ∈ Ps, ∃ d ∈ A, mulP s p = mulP d s) : NormSetOK sA ss := by
  refine ⟨fun l hl hn => ?_, fun s hs p hp => ?_⟩
  · have hl' := VL_elts l hl
    refine mem_cl_of hC hl' (h1 _ (pk_mem_elts hl) fun p' hp' => ?_)
    rw [← hP, List.map_map] at hp'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hp'
    obtain ⟨d, hd, he⟩ := hn p hp
    have hd' := VL_cl sA d hd
    exact ⟨pk d, pk_mem_of hA hd, (mulL_eq_iff hl' (VL_Lx p) hd' hl').1 he⟩
  · obtain ⟨d', hd', he⟩ := h2 _ (pk_Lx_mem hS hs) _ (pk_Lx_mem hP hp)
    obtain ⟨d, hd, rfl⟩ := exists_of_pk_mem hA hd'
    exact ⟨d, hd, (mulL_eq_iff (VL_Lx s) (VL_Lx p) (VL_cl sA d hd) (VL_Lx s)).2 he⟩

theorem centInOK_of (hu : pk (Lx u) = cu) (hA : (cl sA).map pk = A) (hC : (cl ss).map pk = C)
    (hS : (ss.map Lx).map pk = S) (h1 : ∀ c ∈ A, mulP cu c = mulP c cu → c ∈ C)
    (h2 : ∀ s ∈ S, mulP cu s = mulP s cu ∧ s ∈ A) : CentInOK u sA ss := by
  refine ⟨fun l hl hc => ?_, fun s hs => ?_⟩
  · have hl' := VL_cl sA l hl
    refine mem_cl_of hC hl' (h1 _ (pk_mem_of hA hl) ?_)
    rw [← hu]
    exact (mulL_eq_iff (VL_Lx u) hl' hl' (VL_Lx u)).1 hc
  · obtain ⟨h3, h4⟩ := h2 _ (pk_Lx_mem hS hs)
    refine ⟨(mulL_eq_iff (VL_Lx u) (VL_Lx s) (VL_Lx s) (VL_Lx u)).2 ?_, mem_cl_of hA (VL_Lx s) h4⟩
    rw [hu]
    exact h3

theorem disjOK_of (hU : (cl [u]).map pk = A) (hC : (cl ss).map pk = C)
    (h : ∀ c ∈ C, c ∈ A → c = 1459980823972598128486511383358617792788444579872) : DisjOK u ss := by
  intro l hl hl'
  apply VL_inj (VL_cl ss l hl) VL_idL
  rw [pk_idL, idP_eq]
  exact h _ (pk_mem_of hC hl) (pk_mem_of hU hl')

theorem invertOK_of (hu : pk (Lx u) = cu) (hv : pk (Lx v) = cv) (hvi : pk (Lx v⁻¹) = cvi)
    (h : ∀ c ∈ hcElts.E, mulP cu c = mulP c cu → mulP c cv ≠ mulP cvi c) : InvertOK u v := by
  intro l hl hc he
  have hl' := VL_elts l hl
  refine h _ (pk_mem_elts hl) ?_ ?_
  · rw [← hu]
    exact (mulL_eq_iff (VL_Lx u) hl' hl' (VL_Lx u)).1 hc
  · rw [← hv, ← hvi]
    exact (mulL_eq_iff hl' (VL_Lx v) (VL_Lx v⁻¹) hl').1 he

theorem pk_Lx_t : pk (Lx (gA 4)) = cA4 := by decide +kernel

theorem pk_Lx_z : pk (Lx zA) = cZ := by decide +kernel

theorem conjOK_of (hC : (cl ss).map pk = C) (h : ∃ c ∈ C, mulP c cA4 = mulP (mulP cA4 cZ) c) :
    ConjOK ss := by
  obtain ⟨c, hc, he⟩ := h
  obtain ⟨l, hl, rfl⟩ := exists_of_pk_mem hC hc
  have hl' := VL_cl ss l hl
  refine ⟨l, hl, ?_⟩
  rw [mulL_eq_iff hl' (VL_Lx _) (VL_mulL (VL_Lx _) (VL_Lx _)) hl', pk_mulL (VL_Lx _) (VL_Lx _),
    pk_Lx_t, pk_Lx_z]
  exact he

theorem invol_pk {l : List ℕ} (hl : VL l) (h : mulL l l = idL ∧ l ≠ idL ∧ l ≠ Lx zA) :
    mulP (pk l) (pk l) = 1459980823972598128486511383358617792788444579872 ∧
      pk l ≠ 1459980823972598128486511383358617792788444579872 ∧ pk l ≠ cZ := by
  refine ⟨?_, fun e => h.2.1 (VL_inj hl VL_idL ?_), fun e => h.2.2 (VL_inj hl (VL_Lx _) ?_)⟩
  · rw [← pk_mulL hl hl, h.1, pk_idL, idP_eq]
  · rw [e, pk_idL, idP_eq]
  · rw [e, pk_Lx_z]

theorem invKOK_of (hK : (cl sK).map pk = C)
    (h1 : ∀ c ∈ C, (mulP c c = 1459980823972598128486511383358617792788444579872 ∧
      c ≠ 1459980823972598128486511383358617792788444579872 ∧ c ≠ cZ) → c ∈ invK)
    (h2 : ∀ c ∈ invK, ∀ c' ∈ invK, ∃ h ∈ hcElts.E, mulP h c = mulP c' h) : InvKOK := by
  intro l hl hi l' hl' hi'
  have hv := VL_cl sK l hl
  have hv' := VL_cl sK l' hl'
  obtain ⟨c, hc, he⟩ := h2 _ (h1 _ (pk_mem_of hK hl) (invol_pk hv hi)) _
    (h1 _ (pk_mem_of hK hl') (invol_pk hv' hi'))
  rw [← elts_map_pk_eq] at hc
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
  have hg' := VL_elts g hg
  exact ⟨g, hg, (mulL_eq_iff hg' hv hv' hg').2 he⟩

theorem cardCentT_of (h : (hcElts.E.filter fun c => decide (mulP cA4 c = mulP c cA4)).length = 8) :
    CardCentT := by
  change (elts.filter fun l => decide (mulL (Lx (gA 4)) l = mulL l (Lx (gA 4)))).length = 8
  refine Eq.trans ?_ h
  rw [← elts_map_pk_eq, List.filter_map, List.length_map]
  refine congrArg List.length (List.filter_congr fun l hl => ?_)
  have hl' := VL_elts l hl
  refine decide_eq_decide.2 ?_
  rw [← pk_Lx_t]
  exact mulL_eq_iff (VL_Lx _) hl' hl' (VL_Lx _)

theorem pk_Lx_e0 : pk (Lx (gA 0)) = cA0 := by decide +kernel

theorem pk_Lx_e2 : pk (Lx (gA 2)) = cA2 := by decide +kernel

theorem pk_Lx_e0i : pk (Lx (gA 0)⁻¹) = cA0I := by decide +kernel

theorem pk_Lx_e2i : pk (Lx (gA 2)⁻¹) = cA2I := by decide +kernel

theorem pk_Lx_yp : pk (Lx (gA 0 * gA 2)) = cYp := by decide +kernel

theorem pk_Lx_ym : pk (Lx (gA 0 * (gA 2)⁻¹)) = cYm := by decide +kernel

theorem pkS_C1 : (sC1.map Lx).map pk = [cA0, cA2, cA3] := by decide +kernel

theorem pkS_C2 : (sC2.map Lx).map pk = [cA2, cA0, cA1] := by decide +kernel

theorem pkS_N1 : (sN1.map Lx).map pk = [cA0, cA2, cA3, cA4] := by decide +kernel

theorem pkS_N2 : (sN2.map Lx).map pk = [cA2, cA0, cA1, cA4] := by decide +kernel

theorem pkS_PZ : (sPZ.map Lx).map pk = [cA0, cA2, cZ] := by decide +kernel

theorem pkS_PE : (sPE.map Lx).map pk = [cA0, cA2, cA4, cZ] := by decide +kernel

theorem pkS_L1 : (sL1.map Lx).map pk = [cA0, cZ] := by decide +kernel

theorem pkS_L2 : (sL2.map Lx).map pk = [cA2, cZ] := by decide +kernel

theorem pkS_P : (sP.map Lx).map pk = [cA0, cA2] := by decide +kernel

theorem pkS_S1 : ([gA 0].map Lx).map pk = [cA0] := by decide +kernel

theorem pkS_S2 : ([gA 2].map Lx).map pk = [cA2] := by decide +kernel

theorem pkS_Yp : ([gA 0 * gA 2].map Lx).map pk = [cYp] := by decide +kernel

theorem pkS_Ym : ([gA 0 * (gA 2)⁻¹].map Lx).map pk = [cYm] := by decide +kernel

theorem clE_H1 : (cl sH1).map pk = clH1.E := cl_map_pk_row 0
theorem clE_H2 : (cl sH2).map pk = clH2.E := cl_map_pk_row 1
theorem clE_K : (cl sK).map pk = clK.E := cl_map_pk_row 2
theorem clE_P : (cl sP).map pk = clP.E := cl_map_pk_row 3
theorem clE_S1 : (cl [gA 0]).map pk = clS1.E := cl_map_pk_row 4
theorem clE_S2 : (cl [gA 2]).map pk = clS2.E := cl_map_pk_row 5
theorem clE_Yp : (cl [gA 0 * gA 2]).map pk = clYp.E := cl_map_pk_row 6
theorem clE_Ym : (cl [gA 0 * (gA 2)⁻¹]).map pk = clYm.E := cl_map_pk_row 7
theorem clE_C1 : (cl sC1).map pk = clC1.E := cl_map_pk_row 8
theorem clE_C2 : (cl sC2).map pk = clC2.E := cl_map_pk_row 9
theorem clE_N1 : (cl sN1).map pk = clN1.E := cl_map_pk_row 10
theorem clE_N2 : (cl sN2).map pk = clN2.E := cl_map_pk_row 11
theorem clE_PZ : (cl sPZ).map pk = clPZ.E := cl_map_pk_row 12
theorem clE_PE : (cl sPE).map pk = clPE.E := cl_map_pk_row 13
theorem clE_L1 : (cl sL1).map pk = clL1.E := cl_map_pk_row 14
theorem clE_L2 : (cl sL2).map pk = clL2.E := cl_map_pk_row 15
theorem clE_T1 : (cl sT1).map pk = clT1.E := cl_map_pk_row 16
theorem clE_T2 : (cl sT2).map pk = clT2.E := cl_map_pk_row 17

theorem f5Eq : F5Eq := fun _ => rfl

theorem certificate320015_facts : F5Eq ∧ ClosedAt sH1 ∧ ClosedAt sH2 ∧ ClosedAt sK ∧ ClosedAt sP ∧
    PFacts ∧ ClosedAt [gA 0] ∧ ClosedAt [gA 2] ∧ ClosedAt [gA 0 * gA 2] ∧
    ClosedAt [gA 0 * (gA 2)⁻¹] ∧ CentOK (gA 0) sC1 ∧ CentOK (gA 2) sC2 ∧ DisjOK (gA 0) sH2 ∧
    DisjOK (gA 2) sH1 ∧ NormSetOK [gA 0] sN1 ∧ NormSetOK [gA 2] sN2 ∧ Cent2OK (gA 0) (gA 2) sPZ ∧
    NormSetOK sP sPE ∧ CentOK (gA 0 * gA 2) sPZ ∧ NormSetOK [gA 0 * gA 2] sPE ∧
    CentOK (gA 0 * (gA 2)⁻¹) sPZ ∧ NormSetOK [gA 0 * (gA 2)⁻¹] sPE ∧
    InvertOK (gA 0) (gA 2) ∧ InvertOK (gA 2) (gA 0) ∧ ConjOK sT2 ∧ ConjOK sT1 ∧
    CentInOK (gA 0) sH1 sL1 ∧ CentInOK (gA 2) sH2 sL2 ∧ InvKOK ∧ CardCentT := by
  obtain ⟨gc1, gc2, gcp, gcyp, gcym⟩ := chk_gens_cent
  obtain ⟨gn1, gn2, gnp, gnyp, gnym⟩ := chk_gens_norm
  obtain ⟨d1, d2, j2, j1, i1, i1', i2, i2'⟩ := chk_small
  exact ⟨f5Eq, closed_H1, closed_H2, closed_K, closed_P, pFacts, closed_s1, closed_s2, closed_yp,
    closed_ym,
    centOK_of pk_Lx_e0 clE_C1 pkS_C1 chk_cent_1 gc1,
    centOK_of pk_Lx_e2 clE_C2 pkS_C2 chk_cent_2 gc2,
    disjOK_of clE_S1 clE_H2 d1,
    disjOK_of clE_S2 clE_H1 d2,
    normSetOK_of clE_S1 pkS_S1 clE_N1 pkS_N1 chk_norm_1 gn1,
    normSetOK_of clE_S2 pkS_S2 clE_N2 pkS_N2 chk_norm_2 gn2,
    cent2OK_of pk_Lx_e0 pk_Lx_e2 clE_PZ pkS_PZ chk_cent_p gcp,
    normSetOK_of clE_P pkS_P clE_PE pkS_PE chk_norm_p gnp,
    centOK_of pk_Lx_yp clE_PZ pkS_PZ chk_cent_yp gcyp,
    normSetOK_of clE_Yp pkS_Yp clE_PE pkS_PE chk_norm_yp gnyp,
    centOK_of pk_Lx_ym clE_PZ pkS_PZ chk_cent_ym gcym,
    normSetOK_of clE_Ym pkS_Ym clE_PE pkS_PE chk_norm_ym gnym,
    invertOK_of pk_Lx_e0 pk_Lx_e2 pk_Lx_e2i chk_invert_1,
    invertOK_of pk_Lx_e2 pk_Lx_e0 pk_Lx_e0i chk_invert_2,
    conjOK_of clE_T2 j2, conjOK_of clE_T1 j1,
    centInOK_of pk_Lx_e0 clE_H1 clE_L1 pkS_L1 i1 i1',
    centInOK_of pk_Lx_e2 clE_H2 clE_L2 pkS_L2 i2 i2',
    invKOK_of clE_K chk_invK_sub chk_invK_conj, cardCentT_of chk_card_t⟩

end CFSG.KC.HcPack

end
