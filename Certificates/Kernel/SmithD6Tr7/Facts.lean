module

public import Certificates.Kernel.SmithD6Tr7.Checks
public import CFSG.Certificates.Kernel.SmithD6Tr7Sound
public import Certificates.Kernel.SmithD6Uw.Model

set_option maxRecDepth 100000

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.SmithD6Tr7

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem tr7Dim_ok {j : ℕ} (hj : j < 7) : tr7DimK j = true := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | j
  exacts [tr7Dim0_ok, tr7Dim1_ok, tr7Dim2_ok, tr7Dim3_ok, tr7Dim4_ok, tr7Dim5_ok, tr7Dim6_ok,
    absurd hj (by omega)]

theorem tr7Head_ok {a : ℕ} (ha : a < 5) : tr7HeadK a = true ∧ tr7ForestOK a (tr7Dim a) = true := by
  rcases a with _ | _ | _ | _ | _ | a
  exacts [⟨tr7Head0_ok, tr7Forest0_ok⟩, ⟨tr7Head1_ok, tr7Forest1_ok⟩, ⟨tr7Head2_ok, tr7Forest2_ok⟩,
    ⟨tr7Head3_ok, tr7Forest3_ok⟩, ⟨tr7Head4_ok, tr7Forest4_ok⟩, absurd ha (by omega)]

theorem wt_zero (hW : wtArr.toList = J.wtC.flatten) : wt 0 = 1 := by
  obtain ⟨h0, h1⟩ := SmithD6Uw.wt0
  rw [SmithD6Uw.wt_eq hW h0, h1]

theorem zip_facts {GP : List (ℕ × ℕ)} {Ms : List (List ℕ)} (hlen : Ms.length = GP.length)
    {P : (ℕ × ℕ) × List ℕ → Prop} (h : ∀ e ∈ GP.zip Ms, P e) :
    ∀ i (hi : i < GP.length), P (GP[i], Ms[i]'(hlen ▸ hi)) := by
  intro i hi
  have hz : i < (GP.zip Ms).length := by simp [List.length_zip, hlen, hi]
  have := h _ (List.getElem_mem hz)
  rwa [List.getElem_zip] at this

section Model

variable (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
  (hW : wtArr.toList = J.wtC.flatten)
include hL hW

theorem tr7ChkDim_of_pinned {j : ℕ} (hj : j < 7) : tr7ChkDim j = true := by
  have hd := tr7Dim_ok hj
  unfold tr7DimK at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨hrep, hind⟩, hlt⟩, hlen⟩, hw⟩ := hd
  unfold tr7ChkDim tr7Bs32
  rw [tr7Cols32_eq hL hrep]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨hind, hlt⟩, hlen⟩, ?_⟩
  by_cases hc : (j == 2 || j == 6) = true
  · rw [if_pos hc] at hw ⊢
    simp only [Bool.and_eq_true] at hw
    refine List.any_eq_true.2 ⟨0, List.mem_range.2 (by norm_num), ?_⟩
    rw [wt_zero hW, tr7RepCols_apply hL hw.1 (by norm_num)]
    exact hw.2
  · rw [if_neg hc] at hw ⊢

theorem tr7ChkDims_of_pinned : tr7ChkDims = true :=
  List.all_eq_true.2 fun _ hj => tr7ChkDim_of_pinned hL hW (List.mem_range.1 hj)

theorem tr7M1_rec_of_pinned {a : ℕ} (ha : a < 5) :
    (∀ k ∈ tr7Gens (tr7J a), k < 365211 ∧ tr7RepImg (tr7J a) k = k) ∧
    wtIdx (tr7Target (tr7J a)) < 75735 ∧
    (∀ v ∈ tr7Cols32 (tr7J a), tr7Red (tr7Ech (tr7Cols32 (tr7J a))) v = 0) ∧
    ∀ m < 2 ^ (tr7Bs32 (tr7J a)).length, tr7XorSel (tr7Bs32 (tr7J a)) m = 0 ∨
      ∀ U : Submodule (ZMod 2) V, (∀ k ∈ tr7Gens (tr7J a), ∀ c, decode32 c ∈ U →
        decode32 (applyCols (tvCols k) c) ∈ U) →
        decode32 (tr7XorSel (tr7Bs32 (tr7J a)) m) ∈ U → decode32 (tr7Target (tr7J a)) ∈ U := by
  obtain ⟨hH, hF⟩ := tr7Head_ok ha
  unfold tr7HeadK at hH
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hH
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hrep, hdim⟩, hred⟩, hlenM⟩, hle8⟩, hgens⟩, hmem⟩, htc⟩, hroots⟩ := hH
  have hc32 := tr7Cols32_eq hL hrep
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    unfold tr7Gens at hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨⟨h1, h2⟩, -⟩ := zip_facts hlenM hgens i hi
    exact ⟨(tr7Line_facts hL h1).1, tr7RepImg_fix hL h2⟩
  · obtain ⟨-, -, hf, hs⟩ := SmithD6Trees.wt_facts
    exact (SmithD6Uw.wtIdx_lt_iff hW _).2 ((SmithD6Uw.memB_iff_mem hf hs _).1 hmem)
  · rw [hc32]
    exact hred
  · intro m hm
    unfold tr7Bs32 at hm ⊢
    rw [hc32] at hm ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact Or.inl (tr7XorSel_zero _)
    refine Or.inr fun U hU hn => ?_
    rw [← htc]
    have hM : ∀ g < (JTr.tr7M.getD a []).length, ∀ m',
        decode32 (tr7XorSel (tr7Bs (tr7ColsK (tr7J a))) m') ∈ U →
        decode32 (tr7XorSel (tr7Bs (tr7ColsK (tr7J a)))
          (tr7XorSel ((JTr.tr7M.getD a []).getD g []) m')) ∈ U := by
      intro g hg m' hm'
      have hgi : g < (tr7GenPairs (tr7J a)).length := hlenM ▸ hg
      obtain ⟨⟨h1, -⟩, h3⟩ := zip_facts hlenM hgens g hgi
      rw [List.getD_eq_getElem _ _ hg]
      have hk : lineOf (tr7GenPairs (tr7J a))[g].1 (tr7GenPairs (tr7J a))[g].2 ∈
          tr7Gens (tr7J a) := by
        unfold tr7Gens
        exact List.mem_map.2 ⟨_, List.getElem_mem hgi, rfl⟩
      exact tr7Mat_mem (k := lineOf (tr7GenPairs (tr7J a))[g].1 (tr7GenPairs (tr7J a))[g].2)
        (tr7Line_facts hL h1).2 h3 (hU _ hk) m' hm'
    have hR : ∀ r ∈ JTr.tr7Reps.getD a [],
        decode32 (tr7XorSel (tr7Bs (tr7ColsK (tr7J a))) r) ∈ U →
        decode32 (tr7XorSel (tr7Bs (tr7ColsK (tr7J a))) (JTr.tr7T.getD a 0)) ∈ U :=
      fun r hr hrU => tr7Root_mem hM (hroots r hr) hrU
    unfold tr7ForestOK at hF
    exact tr7Forest_mem hM (by omega) hR hF m (by rw [← hdim]; exact hm) hm0 hn

theorem tr7M1_of_pinned {j : ℕ} (hj : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5) :
    (∀ k ∈ tr7Gens j, k < 365211 ∧ tr7RepImg j k = k) ∧ wtIdx (tr7Target j) < 75735 ∧
    (∀ v ∈ tr7Cols32 j, tr7Red (tr7Ech (tr7Cols32 j)) v = 0) ∧
    ∀ m < 2 ^ (tr7Bs32 j).length, tr7XorSel (tr7Bs32 j) m = 0 ∨
      ∀ U : Submodule (ZMod 2) V, (∀ k ∈ tr7Gens j, ∀ c, decode32 c ∈ U →
        decode32 (applyCols (tvCols k) c) ∈ U) →
        decode32 (tr7XorSel (tr7Bs32 j) m) ∈ U → decode32 (tr7Target j) ∈ U := by
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact tr7M1_rec_of_pinned hL hW (a := 0) (by norm_num)
  · exact tr7M1_rec_of_pinned hL hW (a := 1) (by norm_num)
  · exact tr7M1_rec_of_pinned hL hW (a := 2) (by norm_num)
  · exact tr7M1_rec_of_pinned hL hW (a := 3) (by norm_num)
  · exact tr7M1_rec_of_pinned hL hW (a := 4) (by norm_num)

end Model

end CertificateChecks.SmithD6Tr7

end
