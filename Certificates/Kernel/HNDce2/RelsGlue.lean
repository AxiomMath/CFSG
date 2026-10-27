module

public import Certificates.Kernel.HNDce2.Rels
public import Certificates.Kernel.HNDce2.Cover
public import CFSG.Certificates.Kernel.TwistDce2.RelsSound
public import CFSG.Sporadic.Recognition.CoverChainSub

public section

namespace CFSG.KD.HNDce2

open CFSG.Certificates.TwDce2.Rels CFSG.Sporadic.Recognition.HNMultiplier CFSG.CosetTable
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe CFSG.KC.YModel
open scoped commutatorElement

theorem hnRCodes_len : ∀ w ∈ hnRCodes, w.length < 2 ^ 32 := by decide +kernel

theorem hnInv_ok : CFSG.KC.TwDce2.invCodesOK INVM 6 = true :=
  (CFSG.Certificates.TwDce.Words.andB_iff.1 node1_ok).2

noncomputable abbrev hnAct (m : ℕ) := tableHom letters_ok m

theorem letterCode_ofCodes : ∀ x < 14,
    letterCode ((⟨x / 2 % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7), decide (x % 2 = 0)) = x := by
  decide

theorem base_one {c : List ℕ} (hc : c ∈ hnRCodes) : hnAct 7 (FreeGroup.mk (ofCodes c)) = 1 := by
  obtain ⟨hlt, hfix⟩ := relsOK_sound rels_ok hnRCodes_len c hc
  refine tableHom_mk_eq_one letters_ok hnInv_ok ?_ ?_
  · intro l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    have := hlt x hx
    change x / 2 % 7 < 6
    omega
  · have e : (ofCodes c).map letterCode = c := by
      rw [ofCodes, List.map_map]
      conv_rhs => rw [← List.map_id c]
      exact List.map_congr_left fun x hx => letterCode_ofCodes x (by have := hlt x hx; omega)
    rw [e]
    exact hfix

theorem relsMid_one {r : List (Fin 7 × Bool)} (hr : r ∈ hnRelsMid) :
    hnAct 7 (FreeGroup.mk r) = 1 := by
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
    exact base_one (by simp [hnRCodes, hc])
  · rw [List.mem_singleton.1 hr]
    exact base_one (by simp [hnRCodes])

theorem rels2_one {r : List (Fin 7 × Bool)} (hr : r ∈ hnRels2) :
    hnAct 7 (FreeGroup.mk r) = 1 := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  exact base_one (by simp [hnRCodes, hc])

theorem nwords_one {r : List (Fin 7 × Bool)} (hr : r ∈ hnNwords) :
    hnAct 7 (FreeGroup.mk r) = 1 := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  exact base_one (by simp [hnRCodes, hc])

theorem hnX_ofCodes : ∀ i : Fin 7, i.val < 5 →
    ofCodes ((2 * i.val + 1) :: commCodes (hnCommCodes i)) = (i, false) :: hnCommWord i := by
  decide +kernel

theorem mem_five : ∀ i : Fin 7, i.val < 5 → i ∈ ([0, 1, 2, 3, 4] : List (Fin 7)) := by decide

theorem commWord_t : ∀ i : Fin 7, 5 ≤ i.val → ∃ l ∈ hnCommWord i, 6 ≤ l.1.val := by
  decide +kernel

theorem xw_one {i : Fin 7} (hi : i.val < 5) :
    hnAct 7 (FreeGroup.mk ((i, false) :: hnCommWord i)) = 1 := by
  rw [← hnX_ofCodes i hi]
  refine base_one ?_
  have h : (2 * i.val + 1) :: commCodes (hnCommCodes i) ∈ hnXCodes :=
    List.mem_map.2 ⟨i, mem_five i hi, rfl⟩
  simp [hnRCodes, h]

theorem cover_one {R₀ : List (List (Fin 7 × Bool))}
    (hR : ∀ r ∈ R₀, hnAct 7 (FreeGroup.mk r) = 1) {u : List (Fin 7 × Bool)}
    (hu : u ∈ cover₂Words R₀ hnCommWord) (h6 : ∀ l ∈ u, l.1.val < 6) :
    hnAct 7 (FreeGroup.mk u) = 1 := by
  rcases mem_cover₂Words.1 hu with hu | hu
  · simp only [coverWords, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_finRange, true_and] at hu
    rcases hu with ⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩
    · rw [mk_commWord, map_commutatorElement, hR r hr, commutatorElement_one_right]
    · by_cases hi : i.val < 5
      · exact xw_one hi
      · obtain ⟨l, hl, hl6⟩ := commWord_t i (by omega)
        exact absurd (h6 l (List.mem_cons_of_mem _ hl)) (by omega)
  · simp only [squareWords, List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    rw [← FreeGroup.mul_mk, map_mul, hR r hr, mul_one]

theorem hnTL_length : hnTL.length = 6 := by decide

theorem hnTL_get : ∀ j : Fin hnTL.length, (hnTL.get j).val = j.val := by decide
theorem hnS1L_get : ∀ j : Fin hnS1L.length, (hnS1L.get j).val = j.val := by decide
theorem hnS2L_get : ∀ j : Fin hnS2L.length, (hnS2L.get j).val = j.val := by decide

theorem act_renumber {k : ℕ} {S : List (Fin k)} (hS : ∀ j : Fin S.length, (S.get j).val = j.val)
    {u : List (Fin k × Bool)} {v : List (Fin S.length × Bool)} (h : renumber S u = some v) :
    hnAct S.length (FreeGroup.mk v) = hnAct k (FreeGroup.mk u) := by
  rw [← map_renumber S u v h, hnAct, hnAct, tableHom, tableHom, FreeGroup.lift_mk,
    FreeGroup.lift_mk, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, hS l.1]

theorem lt_six_of_renumber {u : List (Fin 7 × Bool)} {v : List (Fin hnTL.length × Bool)}
    (h : renumber hnTL u = some v) : ∀ l ∈ u, l.1.val < 6 := by
  rw [← map_renumber hnTL u v h]
  intro l hl
  obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
  have h1 := l'.1.isLt
  have h6 := hnTL_length
  change (hnTL.get l'.1).val < 6
  rw [hnTL_get]
  omega

@[expose] def hnEmb2 (w : List (Fin hnS1L.length × Bool)) : List (Fin hnTL.length × Bool) :=
  w.map fun l => (hnS1L.get l.1, l.2)

@[expose] def hnEmb1 (w : List (Fin hnS2L.length × Bool)) : List (Fin hnTL.length × Bool) :=
  hnEmb2 (w.map fun l => (hnS2L.get l.1, l.2))

@[expose] def hnR : List (List (Fin hnTL.length × Bool)) :=
  hnL3 ++ hnL2.map hnEmb2 ++ hnL1.map hnEmb1

theorem hnR_one : ∀ r ∈ hnR, hnAct hnTL.length (FreeGroup.mk r) = 1 := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨u, hu, hur⟩ := List.mem_filterMap.1 hr
      rw [act_renumber hnTL_get hur]
      exact nwords_one hu
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      obtain ⟨v, hv, hvw⟩ := List.mem_filterMap.1 hw
      have e : hnEmb2 w = v := map_renumber _ _ _ hvw
      rw [e]
      obtain ⟨u, hu, huv⟩ := List.mem_filterMap.1 hv
      rw [act_renumber hnTL_get huv]
      exact cover_one (fun r hr => relsMid_one hr) hu (lt_six_of_renumber huv)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    obtain ⟨v₁, hv₁, h₁⟩ := List.mem_filterMap.1 hw
    have e₁ : w.map (fun l => (hnS2L.get l.1, l.2)) = v₁ := map_renumber _ _ _ h₁
    obtain ⟨v₂, hv₂, h₂⟩ := List.mem_filterMap.1 hv₁
    have e₂ : hnEmb2 v₁ = v₂ := map_renumber _ _ _ h₂
    rw [hnEmb1, e₁, e₂]
    obtain ⟨u, hu, huv⟩ := List.mem_filterMap.1 hv₂
    rw [act_renumber hnTL_get huv]
    exact cover_one (fun r hr => rels2_one hr) hu (lt_six_of_renumber huv)

theorem renumber_map_get {k : ℕ} {S : List (Fin k)} (hS : S.Nodup) :
    ∀ w : List (Fin S.length × Bool), renumber S (w.map fun l => (S.get l.1, l.2)) = some w
  | [] => rfl
  | l :: w => by
    have hi : S.finIdxOf? (S.get l.1) = some l.1 := by
      rw [List.finIdxOf?_eq_some_iff]
      refine ⟨rfl, fun j hj e => ?_⟩
      exact absurd ((List.Nodup.get_inj_iff hS).1 e) (Fin.ne_of_lt hj)
    simp only [List.map_cons, renumber, hi, renumber_map_get hS w]

theorem hnS1L_nodup : hnS1L.Nodup := by decide
theorem hnS2L_nodup : hnS2L.Nodup := by decide

theorem hnL3_sub : ∀ w ∈ hnL3, w ∈ hnR := fun w hw =>
  List.mem_append_left _ (List.mem_append_left _ hw)

theorem hnL2_sub : ∀ w ∈ hnL2, w ∈ restrictWords (subsetOf hnTL.length [0, 1, 2, 3, 4]) hnR :=
  fun w hw => List.mem_filterMap.2 ⟨hnEmb2 w,
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hw)),
    renumber_map_get hnS1L_nodup w⟩

theorem hnL1_sub : ∀ w ∈ hnL1, w ∈ restrictWords
    (subsetOf (subsetOf hnTL.length [0, 1, 2, 3, 4]).length [0, 1])
    (restrictWords (subsetOf hnTL.length [0, 1, 2, 3, 4]) hnR) :=
  fun w hw => List.mem_filterMap.2
   ⟨w.map fun l : Fin hnS2L.length × Bool => (hnS2L.get l.1, l.2),
    List.mem_filterMap.2 ⟨hnEmb1 w, List.mem_append_right _ (List.mem_map_of_mem hw),
      renumber_map_get hnS1L_nodup
        (w.map fun l : Fin hnS2L.length × Bool => (hnS2L.get l.1, l.2))⟩,
    renumber_map_get hnS2L_nodup w⟩

abbrev hnPR : Type := PG hnTL.length hnR

noncomputable def hnRho : hnPR →* (Equiv.Perm (Fin 1408))ᵐᵒᵖ :=
  PresentedGroup.toGroup (f := fun j : Fin hnTL.length => tableGen letters_ok j.val) (by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact hnR_one r hr)

theorem hnRho_of (j : Fin hnTL.length) :
    hnRho (PresentedGroup.of j) = tableGen letters_ok j.val :=
  PresentedGroup.toGroup.of _

@[expose] noncomputable def hnPt (g : hnPR) (p : ℕ) : ℕ :=
  if h : p < 1408 then ((hnRho g).unop ⟨p, h⟩).val else p

theorem hnPt_lt {g : hnPR} {p : ℕ} (hp : p < 1408) : hnPt g p < 1408 := by
  rw [hnPt, dif_pos hp]
  exact Fin.isLt _

theorem hnPt_one (p : ℕ) : hnPt 1 p = p := by
  unfold hnPt
  split_ifs <;> simp

theorem hnPt_mul (a b : hnPR) (p : ℕ) : hnPt (a * b) p = hnPt b (hnPt a p) := by
  by_cases hp : p < 1408
  · have ha : hnPt a p = ((hnRho a).unop ⟨p, hp⟩).val := by rw [hnPt, dif_pos hp]
    rw [hnPt, dif_pos hp, hnPt, dif_pos (hnPt_lt hp), map_mul, MulOpposite.unop_mul,
      Equiv.Perm.mul_apply]
    congr 2
    exact Fin.ext ha.symm
  · have ha : hnPt a p = p := by rw [hnPt, dif_neg hp]
    rw [hnPt, dif_neg hp, ha, hnPt, dif_neg hp]

@[expose] noncomputable def hnX (c : ℕ) : hnPR :=
  if c % 2 = 0 then PresentedGroup.of ⟨c / 2 % hnTL.length, Nat.mod_lt _ (by decide)⟩
  else (PresentedGroup.of ⟨c / 2 % hnTL.length, Nat.mod_lt _ (by decide)⟩)⁻¹

theorem hnPt_x {c : ℕ} (hc : c < 12) {p : ℕ} (hp : p < 1408) :
    fieldAt 11 (F c) p = hnPt (hnX c) p := by
  have hj : c / 2 % hnTL.length = c / 2 := by rw [hnTL_length]; omega
  rw [hnPt, dif_pos hp, hnX]
  split_ifs with h2
  · rw [hnRho_of]
    simp only [hj]
    rw [tableGen_apply letters_ok (by omega)]
    congr 2
    omega
  · rw [map_inv, hnRho_of]
    simp only [hj]
    rw [tableGen_inv_apply letters_ok hnInv_ok (by omega)]
    congr 2
    omega

theorem hnF_lt {c : ℕ} (hc : c < 12) {p : ℕ} (hp : p < 1408) : fieldAt 11 (F c) p < 1408 :=
  ((lettersOK_sound letters_ok c hc).2 p hp).1

theorem hnPt_evalWord : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → ∀ {p : ℕ}, p < 1408 →
    hnPt (CFSG.Certificates.CosetEnumeration.evalWord hnX w) p =
      w.foldl (fun q c => fieldAt 11 (F c) q) p
  | [], _, p, _ => hnPt_one p
  | c :: w, hw, p, hp => by
    have hc := hw c List.mem_cons_self
    rw [CFSG.Certificates.CosetEnumeration.evalWord, List.map_cons, List.prod_cons, hnPt_mul,
      ← hnPt_x hc hp, List.foldl_cons]
    exact hnPt_evalWord w (fun d hd => hw d (List.mem_cons_of_mem _ hd)) (hnF_lt hc hp)

theorem node1_fix : ∀ c ∈ CFSG.KC.LaneChain.getL CG 1,
    CFSG.KC.TwDce2.evP F (CFSG.KC.TwDce2.gWord INVM RW c) 0 = 0 :=
  fixesPt_sound (CFSG.Certificates.TwDce.Words.andB_iff.1 node1_ok).1

theorem card_hnPR_le {k₃ k₂ k₁ c₃ c₂ c₁ : ℕ}
    (e₃ : subsetCheckShortCC hnL3 [0, 1, 2, 3, 4] k₃ c₃ 2 = true)
    (e₂ : subsetCheckShortCC hnL2 [0, 1] k₂ c₂ 704 = true)
    (e₁ : subsetCheckShortCC hnL1 [] k₁ c₁ 126000 = true) :
    Finite hnPR ∧ Nat.card hnPR ≤ 177408000 := by
  obtain ⟨f, c⟩ := card_PG_le_chain₃_sub (ws := hnR) (S₁ := [0, 1, 2, 3, 4]) (S₂ := [0, 1])
    hnL3_sub hnL2_sub hnL1_sub e₃ e₂ e₁
  exact ⟨f, c.trans (by norm_num)⟩

end CFSG.KD.HNDce2

end
