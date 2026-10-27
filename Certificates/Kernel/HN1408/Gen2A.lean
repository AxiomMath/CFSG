module

public import Certificates.Kernel.HN1408.Basic
public import Certificates.Kernel.HN1408.Gen2AChecks

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CompatModel
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem gen2aU_length : gen2aU.length = 4 := by decide

theorem gen2aU_letters : ∀ k < 4, lettersOK (gen2aU.getD k []) = true ∧
    lettersOK (gen2aU.getD k []).reverse = true := by decide

theorem u_spec {k : Nat} (hk : k < 4) :
    (bIf(commP (WK (gen2aU.getD k [])) (WK gen2aC1), true,
      commP (WK (gen2aU.getD k [])) (WK gen2aC2))) = true ∧
    invEqK 1408 11 (mask 11) (1408 * 11) (WK (gen2aU.getD k [])) (WK (gen2aU.getD k []).reverse) =
      true ∧
    invEqK 1408 11 (mask 11) (1408 * 11) (WK (gen2aU.getD k []).reverse) (WK (gen2aU.getD k [])) =
      true := by
  have h := allN_spec k2u k hk
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem mem_gen2aU {u : List Nat} (hu : u ∈ gen2aU) : ∃ k < 4, gen2aU.getD k [] = u := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
  refine ⟨k, by rw [← gen2aU_length]; exact hk, ?_⟩
  simp [List.getD_eq_getElem?_getD, hk]

theorem mem_gen2aProd {p : ℕ × List ℕ} (hp : p ∈ gen2aProd) :
    ∃ j < 7, gen2aProd.getD j (0, []) = p := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  have hl : gen2aProd.length = 7 := by decide
  refine ⟨j, by rw [← hl]; exact hj, ?_⟩
  simp [List.getD_eq_getElem?_getD, hj]

theorem prod_letters : ∀ j < 7, ∀ l ∈ (gen2aProd.getD j (0, [])).2, 1 ≤ l ∧ l ≤ 8 := by
  decide

theorem tabU_eq {k : Nat} (hk : k < 4) :
    tabW (gen2aU.getD k []) = tabT (unpack 1408 11 (WK (gen2aU.getD k []))) ∧
      Cn (WK (gen2aU.getD k [])) :=
  tabW_eq (gen2aU_letters k hk).1

theorem tabUI_eq {k : Nat} (hk : k < 4) :
    invT 1408 (tabW (gen2aU.getD k [])) = tabT (unpack 1408 11 (WK (gen2aU.getD k []).reverse)) ∧
      Cn (WK (gen2aU.getD k []).reverse) := by
  rw [(tabU_eq hk).1, invT_unpack (by norm_num) (u_spec hk).2.1]
  exact ⟨rfl, (tabW_eq (gen2aU_letters k hk).2).2⟩

theorem tabs_getD {l : Nat} (h1 : 1 ≤ l) (h8 : l ≤ 8) :
    gen2aTabs.getD (l - 1) (idT 1408) = tabT (unpack 1408 11 (UL l)) ∧ Cn (UL l) := by
  have hm : (gen2aU.map List.reverse).length = 4 := by simp [gen2aU_length]
  unfold UL gen2aTabs
  by_cases h : l - 1 < 4
  · have e1 : (gen2aU.map tabW ++ (gen2aU.map tabW).map (invT 1408)).getD (l - 1) (idT 1408) =
        tabW (gen2aU.getD (l - 1) []) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, gen2aU_length, h]
    have e2 : (gen2aU ++ gen2aU.map List.reverse).getD (l - 1) [] = gen2aU.getD (l - 1) [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, gen2aU_length, h]
    rw [e1, e2]
    exact tabU_eq h
  · have hk : l - 1 - 4 < 4 := by omega
    have e1 : (gen2aU.map tabW ++ (gen2aU.map tabW).map (invT 1408)).getD (l - 1) (idT 1408) =
        invT 1408 (tabW (gen2aU.getD (l - 1 - 4) [])) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, gen2aU_length, hk,
        Nat.le_of_not_lt h]
    have e2 : (gen2aU ++ gen2aU.map List.reverse).getD (l - 1) [] =
        (gen2aU.getD (l - 1 - 4) []).reverse := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, gen2aU_length, hk,
        Nat.le_of_not_lt h]
    rw [e1, e2]
    exact tabUI_eq hk

theorem gen2aOK_of : gen2aOK = true := by
  have eA := tabW_eq (wd := wordA) (by decide)
  have eB := tabW_eq (wd := wordB) (by decide)
  have e1 := tabW_eq (wd := gen2aC1) (by decide)
  have e2 := tabW_eq (wd := gen2aC2) (by decide)
  have eG := tabW_eq (wd := gen2aG) (by decide)
  have ha := k2a
  simp only [bAnd_iff, Bool.not_eq_true'] at ha
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := ha
  have hgens : gensOK = true := gens_all
  have hbasic : gen2aBasicOK = true := by
    unfold gen2aBasicOK
    simp only [hgens, eA.1, eB.1, e1.1, e2.1, eG.1]
    rw [compT_unpack eA.2 eB.2, involOK_eq e1.2,
      involOK_eq e2.2, commTT_eq e1.2 eB.2, commTT_eq e2.2 eB.2, tblEq_eq e1.2 eA.2,
      tblEq_eq e1.2 eB.2, tblEq_eq e1.2 (canonK_pcomp eA.2 eB.2), tblEq_eq e2.2 eA.2,
      tblEq_eq e2.2 eB.2, tblEq_eq e2.2 (canonK_pcomp eA.2 eB.2), commTT_eq eG.2 e1.2,
      commTT_eq eG.2 e2.2, commTT_eq eG.2 eB.2]
    simp only [pc] at a7 a10
    rw [a1, a2, a3, a4, a11, a12, a5, a6, a7, a8, a9, a10, a13]
    decide
  have hgen : gen2aGenOK = true := by
    unfold gen2aGenOK
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨hgens, by decide⟩, by decide⟩, by decide⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
      obtain ⟨k, hk, rfl⟩ := mem_gen2aU hu
      have hs := (u_spec hk).1
      rw [(tabU_eq hk).1, e1.1, e2.1, commTT_eq (tabU_eq hk).2 e1.2,
        commTT_eq (tabU_eq hk).2 e2.2]
      revert hs
      cases commP (WK (gen2aU.getD k [])) (WK gen2aC1) <;> simp
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
      obtain ⟨k, hk, rfl⟩ := mem_gen2aU hu
      rw [(tabUI_eq hk).1, (tabU_eq hk).1]
      exact invOK_unpack (tabU_eq hk).2 (tabUI_eq hk).2 (u_spec hk).2.1
    · intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
        obtain ⟨k, hk, rfl⟩ := mem_gen2aU hu
        rw [(tabU_eq hk).1]
        exact permOK_unpack (tabU_eq hk).2 (u_spec hk).2.1
      · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht'
        obtain ⟨k, hk, rfl⟩ := mem_gen2aU hu
        rw [(tabUI_eq hk).1]
        exact permOK_unpack (tabUI_eq hk).2 (u_spec hk).2.2
    · intro p hp
      obtain ⟨j, hj7, rfl⟩ := mem_gen2aProd hp
      have hl := prod_letters j hj7
      refine ⟨fun l hl' => decide_eq_true (hl l hl'), ?_⟩
      have hw := wordTbl_unpack (gs := gen2aTabs) (S := UL) idT_eq cId
        (wd := (gen2aProd.getD j (0, [])).2) fun l hl' => tabs_getD (hl l hl').1 (hl l hl').2
      have hk := allN_spec k2p j hj7
      simp only [bAnd_iff, Nat.blt_eq] at hk
      rw [hw.1, h1408T_eq hk.1, tblEq_eq hw.2 (h8 hk.1).1]
      exact hk.2
  unfold gen2aOK
  rw [hbasic, hgen]
  rfl

end CFSG.KD.HN1408

end
