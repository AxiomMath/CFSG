module

public import Certificates.Kernel.HcReplay.Subs
public import Certificates.Kernel.HcReplay.EltsGlue
public import CFSG.Certificates.Kernel.HcClosSound
import all Certificates.Data.Kernel.HcPack
import all Certificates.Data.G23RecogGlueInputs
import all Certificates.Data.G23RecogHFactsInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData

@[expose] def subL : List (List ↥Hc) :=
  [sH1, sH2, sK, sP, [gA 0], [gA 2], [gA 0 * gA 2], [gA 0 * (gA 2)⁻¹], sC1, sC2, sN1, sN2, sPZ,
    sPE, sL1, sL2, sT1, sT2]

theorem subL_map_pk : ∀ i : Fin 18, (gensOf (subL.getD i [])).map pk = (subRow i).1 := by
  decide +kernel

theorem cl_map_pk_row (i : Fin 18) : (cl (subL.getD i [])).map pk = (subRow i).2.1 := by
  rw [cl_map_pk, subL_map_pk i, bfsP, idP_eq]
  exact bfsAux_of_replayB _ _ _ _ _ _ _ _ (subR_replay i)

theorem idP_mem_row : ∀ i : Fin 8, idP ∈ (subRow i).2.1 := by decide +kernel

theorem closedAt_of_pk (ss : List ↥Hc) (h0 : idP ∈ (cl ss).map pk)
    (hc : ∀ x ∈ (cl ss).map pk, ∀ g ∈ (gensOf ss).map pk, mulP x g ∈ (cl ss).map pk) :
    ClosedAt ss := by
  refine ⟨?_, fun l hl g hg => ?_⟩
  · rw [mem_iff_pk (VL_cl ss) VL_idL, pk_idL]
    exact h0
  · have hvl := VL_cl ss l hl
    have hvg := VL_gensOf ss g hg
    rw [mem_iff_pk (VL_cl ss) (VL_mulL hvl hvg), pk_mulL hvl hvg]
    exact hc _ (List.mem_map_of_mem hl) _ (List.mem_map_of_mem hg)

theorem closedAt_row (i : Fin 8) : ClosedAt (subL.getD i []) := by
  have hE := cl_map_pk_row ⟨i, by omega⟩
  have hg := subL_map_pk ⟨i, by omega⟩
  refine closedAt_of_pk _ ?_ ?_
  · rw [hE]
    exact idP_mem_row i
  · rw [hE, hg]
    exact closB_sound mulP _ _ _ _ (subR_clos i)

theorem closed_H1 : ClosedAt sH1 := closedAt_row 0

theorem closed_H2 : ClosedAt sH2 := closedAt_row 1

theorem closed_K : ClosedAt sK := closedAt_row 2

theorem closed_P : ClosedAt sP := closedAt_row 3

theorem closed_s1 : ClosedAt [gA 0] := closedAt_row 4

theorem closed_s2 : ClosedAt [gA 2] := closedAt_row 5

theorem closed_yp : ClosedAt [gA 0 * gA 2] := closedAt_row 6

theorem closed_ym : ClosedAt [gA 0 * (gA 2)⁻¹] := closedAt_row 7

theorem clP_facts : clP.E.length = 9 ∧ clP.E.Nodup ∧
    (∀ c ∈ clP.E, mulP c (mulP c c) = idP) ∧ ∀ c ∈ clP.E, ∀ c' ∈ clP.E, mulP c c' = mulP c' c := by
  decide +kernel

theorem pFacts : PFacts := by
  have hE : (cl sP).map pk = clP.E := cl_map_pk_row 3
  obtain ⟨h1, h2, h3, h4⟩ := clP_facts
  have hv := VL_cl sP
  refine ⟨by rw [← h1, ← hE, List.length_map], List.Nodup.of_map pk (by rwa [hE]),
    fun l hl => ?_, fun l hl l' hl' => ?_⟩
  · apply VL_inj (VL_mulL (hv l hl) (VL_mulL (hv l hl) (hv l hl))) VL_idL
    rw [pk_mulL (hv l hl) (VL_mulL (hv l hl) (hv l hl)), pk_mulL (hv l hl) (hv l hl), pk_idL]
    exact h3 _ (hE ▸ List.mem_map_of_mem hl)
  · apply VL_inj (VL_mulL (hv l hl) (hv l' hl')) (VL_mulL (hv l' hl') (hv l hl))
    rw [pk_mulL (hv l hl) (hv l' hl'), pk_mulL (hv l' hl') (hv l hl)]
    exact h4 _ (hE ▸ List.mem_map_of_mem hl) _ (hE ▸ List.mem_map_of_mem hl')

end CFSG.KC.HcPack

end
