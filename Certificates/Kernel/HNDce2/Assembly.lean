module

public import Certificates.Kernel.HNDce2.RelsGlue
public import Certificates.Kernel.HNDce2.Fold0
public import Certificates.Kernel.HNDce2.Fold1
public import Certificates.Kernel.HNDce2.Chain
public import Certificates.Kernel.HNDce2.TComm
public import Certificates.Kernel.HNDce2.Glue
public import Certificates.Kernel.HNMult.Incl
public import CFSG.Certificates.Kernel.TwistDce2.Sound
public import CFSG.Certificates.Kernel.TwistDce2.ChainSound
public import CFSG.Certificates.Kernel.TwistDce2.Index
public import CFSG.Certificates.Kernel.TwistDce2.Words

public section

namespace CFSG.KD.HNDce2

open CFSG.Certificates.TwDce2.Rels CFSG.Sporadic.Recognition.HNMultiplier CFSG.CosetTable
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe CFSG.KC.YModel
  CFSG.Certificates.CosetEnumeration CFSG.Certificates.TwDce CFSG.Certificates.TwDce.Words
  CFSG.KC.TwDce2 CFSG.Certificates.TwDce2 CFSG.Sporadic.Recognition.CoverTransfer
  CFSG.Sporadic.Recognition.CoverBootstrap

@[expose] def hnCN : List ℕ := [177408000, 126000, 1440, 5040, 80640, 500, 240, 640, 30720]

theorem inv_ok : ∀ c < 12, ivL INVM c = if c % 2 = 0 then c + 1 else c - 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rec_ok : ∀ r < 498, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧
    CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16 ∧ (∀ c ∈ wList (RW r), c < 12) ∧
    (∀ c ∈ wList (RA r), c < 12) ∧
    wList (wInv INVM (RW r)) = (wList (RW r)).reverse.map (ivL INVM) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wd_ok : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    ((wList (WD i)).filter (· != 14) = [] ∨ (wList (WD i)).filter (· != 14) = [12, 13] ∨
      (wList (WD i)).filter (· != 14) = [13, 12] ∨
      ∃ r ∈ hnTopCodes, (wList (WD i)).filter (· != 14) ∈ rotations r) := by
  decide +kernel

theorem top_lt : ∀ r ∈ hnTopCodes, ∀ c ∈ r, c < 14 := by decide +kernel

theorem base_ok : (∀ i < NB, CFSG.KC.TwDce.fld BS (16 * i) 65535 < 1408) ∧
    ∀ b ∈ getLL CB 0, ∃ i < NB,
      CFSG.KC.LaneChain.colDat 11 b / 2 = CFSG.KC.TwDce.fld BS (16 * i) 65535 := by
  decide +kernel

theorem gens_ok : ∀ k < 9, ∀ c ∈ CFSG.KC.LaneChain.getL CG k,
    wBelow 12 (gWord INVM RW c) = true ∧ isStabOf RD 498 k (c / 2) = true := by
  decide +kernel

theorem lens_ok : ∀ k < 9, ∀ m ∈ chainLens ((gRegs INVM RW (CFSG.KC.LaneChain.getL CG k)).map
    fun r => CFSG.KC.TwDce.wLen (r / 2)) (getLL CW k), m < 2 ^ 32 := by
  decide +kernel

theorem gens1_ok : ∀ c ∈ CFSG.KC.LaneChain.getL CG 1, ∀ d ∈ wList (gWord INVM RW c), d < 4 := by
  decide +kernel

theorem cn_sum : ∑ i : Fin 9, 177408000 / CFSG.KC.LaneChain.getN hnCN i = 1539000 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  decide

theorem gWord_eq (c : ℕ) :
    gWord INVM RW c = if c % 2 = 1 then wInv INVM (RW (c / 2)) else RW (c / 2) := by
  unfold gWord
  have h1 : Nat.shiftRight c 1 = c / 2 := by
    rw [show Nat.shiftRight c 1 = c >>> 1 from rfl, Nat.shiftRight_eq_div_pow]
  have h2 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h, if_neg (by norm_num)]
    rfl
  · rw [h, if_pos rfl]
    rfl

theorem ivL_lt {c : ℕ} (hc : c < 12) : ivL INVM c < 12 := by
  rw [inv_ok c hc]; split_ifs <;> omega

theorem evalWord_rev_inv {G : Type*} [Group G] {y : ℕ → G} :
    ∀ {l : List ℕ}, (∀ c ∈ l, y (ivL INVM c) = (y c)⁻¹) →
      evalWord y ((l.reverse).map (ivL INVM)) = (evalWord y l)⁻¹
  | [], _ => by simp [evalWord]
  | c :: l, h => by
    have ih := evalWord_rev_inv (y := y) (l := l) fun d hd => h d (List.mem_cons_of_mem _ hd)
    simp only [evalWord, List.map_map] at ih ⊢
    rw [List.reverse_cons, List.map_append, List.prod_append, ih]
    simp [h c List.mem_cons_self]

theorem gWord_lt {c : ℕ} (hc : c / 2 < 498) : ∀ d ∈ wList (gWord INVM RW c), d < 12 := by
  obtain ⟨-, -, hw, -, hi⟩ := rec_ok (c / 2) hc
  rw [gWord_eq]
  split_ifs
  · rw [hi]
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    exact ivL_lt (hw e (List.mem_reverse.1 he))
  · exact hw

abbrev hnPP : Type := PG 7 hnCoverPlus

theorem hnR_plus : ∀ r ∈ hnR, r ∈ restrictWords hnTL hnCoverPlus := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · exact hnL3_mem_plus r hr
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      obtain ⟨v, hv, hvw⟩ := List.mem_filterMap.1 (hnL2_mem_plus w hw)
      have e : hnEmb2 w = v := map_renumber _ _ _ hvw
      rw [e]
      exact hv
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    obtain ⟨v₁, hv₁, h₁⟩ := List.mem_filterMap.1 (hnL1_mem_plus w hw)
    have e₁ : w.map (fun l : Fin hnS2L.length × Bool => (hnS2L.get l.1, l.2)) = v₁ :=
      map_renumber _ _ _ h₁
    obtain ⟨v₂, hv₂, h₂⟩ := List.mem_filterMap.1 hv₁
    have e₂ : hnEmb2 v₁ = v₂ := map_renumber _ _ _ h₂
    rw [hnEmb1, e₁, e₂]
    exact hv₂

theorem lift_get_mk {m : ℕ} {rels : Set (FreeGroup (Fin m))} (S : List (Fin m))
    (w : List (Fin S.length × Bool)) :
    FreeGroup.lift (fun j => (PresentedGroup.of (S.get j) : PresentedGroup rels))
      (FreeGroup.mk w) = PresentedGroup.mk rels (FreeGroup.mk (w.map fun l => (S.get l.1, l.2))) := by
  rw [CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk, FreeGroup.lift_mk,
    List.map_map]
  rfl

noncomputable def hnPi : hnPR →* hnPP :=
  PresentedGroup.toGroup (f := fun j : Fin hnTL.length => (PresentedGroup.of (hnTL.get j) : hnPP))
    (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      obtain ⟨u, hu, hur⟩ := List.mem_filterMap.1 (hnR_plus r hr)
      rw [lift_get_mk, map_renumber _ _ _ hur]
      exact PresentedGroup.one_of_mem (List.mem_map_of_mem hu))

theorem hnPi_of (j : Fin hnTL.length) : hnPi (PresentedGroup.of j) = PresentedGroup.of (hnTL.get j) :=
  PresentedGroup.toGroup.of _

theorem range_hnPi : hnPi.range = hnHP := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨hnTL.get j, List.get_mem _ _, (hnPi_of j).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := List.get_of_mem hx
    exact ⟨j, by rw [hnPi_of, hj]⟩

@[expose] noncomputable def hnXP (c : ℕ) : hnPP := hnPi (hnX c)

theorem evalWord_hnXP (w : List ℕ) : evalWord hnXP w = hnPi (evalWord hnX w) := by
  simp only [evalWord, map_list_prod, List.map_map]
  rfl

theorem wVal_hnXP (w : ℕ) : wVal hnXP w = hnPi (wVal hnX w) := evalWord_hnXP _

theorem hnX_eq {c : ℕ} (hc : c < 14) :
    hnX c = if c % 2 = 0 then PresentedGroup.of (⟨c / 2 % hnTL.length, Nat.mod_lt _ (by decide)⟩)
      else (PresentedGroup.of (⟨c / 2 % hnTL.length, Nat.mod_lt _ (by decide)⟩))⁻¹ := rfl

theorem hnTL_get_lt {c : ℕ} (hc : c < 12) :
    hnTL.get ⟨c / 2 % hnTL.length, Nat.mod_lt _ (by decide)⟩ = (⟨c / 2, by omega⟩ : Fin 7) := by
  apply Fin.ext
  rw [hnTL_get]
  change c / 2 % hnTL.length = c / 2
  rw [hnTL_length]
  omega

theorem hnXP_eq {c : ℕ} (hc : c < 12) : hnXP c = if c % 2 = 0 then
    PresentedGroup.of (⟨c / 2, by omega⟩ : Fin 7) else (PresentedGroup.of (⟨c / 2, by omega⟩ : Fin 7))⁻¹ := by
  rw [hnXP, hnX]
  split_ifs
  · rw [hnPi_of, hnTL_get_lt hc]
  · rw [map_inv, hnPi_of, hnTL_get_lt hc]

theorem hnX_ivL {c : ℕ} (hc : c < 12) : hnX (ivL INVM c) = (hnX c)⁻¹ := by
  rw [inv_ok c hc]
  have hj : ∀ d e : ℕ, d / 2 = e / 2 →
      (⟨d / 2 % hnTL.length, Nat.mod_lt _ (by decide)⟩ : Fin hnTL.length) =
        ⟨e / 2 % hnTL.length, Nat.mod_lt _ (by decide)⟩ := by
    intro d e h
    simp only [h]
  by_cases h : c % 2 = 0
  · rw [if_pos h]
    simp only [hnX, if_pos h, if_neg (show ¬ (c + 1) % 2 = 0 by omega)]
    rw [hj (c + 1) c (by omega)]
  · rw [if_neg h]
    simp only [hnX, if_neg h, if_pos (show (c - 1) % 2 = 0 by omega), inv_inv]
    rw [hj (c - 1) c (by omega)]

theorem hnXP_ivL {c : ℕ} (hc : c < 12) : hnXP (ivL INVM c) = (hnXP c)⁻¹ := by
  rw [hnXP, hnX_ivL hc, map_inv]
  rfl

theorem wVal_wInv {G : Type*} [Group G] {y : ℕ → G} (hy : ∀ c < 12, y (ivL INVM c) = (y c)⁻¹)
    {r : ℕ} (hr : r < 498) : wVal y (wInv INVM (RW r)) = (wVal y (RW r))⁻¹ := by
  obtain ⟨-, -, hw, -, hi⟩ := rec_ok r hr
  rw [wVal, hi, evalWord_rev_inv fun c hc => hy c (hw c hc)]
  rfl

theorem wVal_gWord {G : Type*} [Group G] {y : ℕ → G} (hy : ∀ c < 12, y (ivL INVM c) = (y c)⁻¹)
    {c : ℕ} (hc : c / 2 < 498) : wVal y (gWord INVM RW c) =
      if c % 2 = 1 then (wVal y (RW (c / 2)))⁻¹ else wVal y (RW (c / 2)) := by
  rw [gWord_eq]
  split_ifs
  · exact wVal_wInv hy hc
  · rfl

theorem evP_pt {w p : ℕ} (hw : ∀ c ∈ wList w, c < 12) (hp : p < 1408) :
    CFSG.KC.TwDce2.evP F w p = hnPt (wVal hnX w) p := by
  rw [CFSG.Certificates.TwDce2.Rels.evP_eq, wVal, hnPt_evalWord _ hw hp]
  rfl

theorem allRange_sound {P : ℕ → Bool} {a : ℕ} :
    ∀ {m : ℕ}, allRange P a m = true → ∀ k < m, P (a + k) = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | m + 1, h, k, hk => by
    change CFSG.KC.andB (allRange P a m) (P (Nat.add a m)) = true at h
    rw [CFSG.Certificates.TwDce2.Words.kandB_iff] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allRange_sound h.1 k hk
    · exact h.2

theorem isStabOf_sound {n k g : ℕ} (h : isStabOf RD n k g = true) :
    g < n ∧ 3 ≤ dKind (RD g) ∧ dKind (RD g) < 5 ∧ dN1 (RD g) = k ∧ dN2 (RD g) = k := by
  unfold isStabOf isEq at h
  simp only [CFSG.Certificates.TwDce2.Words.kandB_iff, andB_iff, Nat.blt_eq, Nat.ble_eq, sB_eq] at h
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5⟩ := h
  exact ⟨h1, h2, h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

noncomputable def hnSt (k : ℕ) : Subgroup hnPR :=
  Subgroup.closure {q | ∃ c, isStabOf RD 498 k (c / 2) = true ∧ q = wVal hnX (gWord INVM RW c)}

noncomputable def hnK (k : ℕ) : Subgroup hnPR :=
  Subgroup.closure {q | ∃ c ∈ CFSG.KC.LaneChain.getL CG k, q = wVal hnX (gWord INVM RW c)}

theorem hnK_le_hnSt {k : ℕ} (hk : k < 9) : hnK k ≤ hnSt k := by
  rw [hnK, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  exact Subgroup.subset_closure ⟨c, (gens_ok k hk c hc).2, rfl⟩

theorem fold_pt {k : ℕ} : ∀ (cs : List ℕ), (∀ c ∈ cs, isStabOf RD 498 k (c / 2) = true) →
    ∀ a : hnPR, ∃ g ∈ hnSt k,
      cs.foldl (fun q c => CFSG.KC.TwDce2.evP F (gWord INVM RW c) q) (hnPt a 0) = hnPt (a * g) 0
  | [], _, a => ⟨1, Subgroup.one_mem _, by rw [mul_one]; rfl⟩
  | c :: cs, h, a => by
    have hc := h c List.mem_cons_self
    have hc2 := (isStabOf_sound hc).1
    obtain ⟨g, hg, he⟩ := fold_pt cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      (a * wVal hnX (gWord INVM RW c))
    refine ⟨wVal hnX (gWord INVM RW c) * g,
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c, hc, rfl⟩) hg, ?_⟩
    rw [List.foldl_cons, evP_pt (gWord_lt hc2) (hnPt_lt (by norm_num)), ← hnPt_mul, he, mul_assoc]

theorem cover_pt {k : ℕ} (hk : k < 9) {p : ℕ} (hp : p < 1408) :
    ∃ f < 498, dKind (RD f) < 3 ∧ dN1 (RD f) = k ∧ dN2 (RD f) < 9 ∧
      ∃ g ∈ hnSt k, p = hnPt ((wVal hnX (RW f))⁻¹ * g) 0 := by
  have hck := allRange_sound cover_ok k hk
  rw [Nat.zero_add] at hck
  obtain ⟨f, hf, hk1, hn1, hn2, cs, hcs, hpe⟩ := coverK_sound hck p hp
  have hw := (rec_ok f hf).2.2.1
  have hy : ∀ c < 12, hnX (ivL INVM c) = (hnX c)⁻¹ := fun c hc => hnX_ivL hc
  have h0 : CFSG.KC.TwDce2.evP F (wInv INVM (RW f)) 0 = hnPt (wVal hnX (RW f))⁻¹ 0 := by
    rw [evP_pt _ (by norm_num), wVal_wInv hy hf]
    rw [(rec_ok f hf).2.2.2.2]
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    exact ivL_lt (hw e (List.mem_reverse.1 he))
  obtain ⟨g, hg, he⟩ := fold_pt cs hcs (wVal hnX (RW f))⁻¹
  rw [h0] at hpe
  refine ⟨f, hf, Nat.blt_eq.mp hk1, hn1, hn2, g, hg, hpe.trans he⟩

noncomputable def hnS0 : Subgroup hnPR where
  carrier := {q | hnPt q 0 = 0}
  mul_mem' {a b} ha hb := by
    have ha' : hnPt a 0 = 0 := ha
    have hb' : hnPt b 0 = 0 := hb
    change hnPt (a * b) 0 = 0
    rw [hnPt_mul, ha', hb']
  one_mem' := hnPt_one 0
  inv_mem' {a} ha := by
    have ha' : hnPt a 0 = 0 := ha
    change hnPt a⁻¹ 0 = 0
    have h := hnPt_mul a a⁻¹ 0
    rw [mul_inv_cancel, hnPt_one, ha'] at h
    exact h.symm

theorem mem_hnS0 {q : hnPR} : q ∈ hnS0 ↔ hnPt q 0 = 0 := Iff.rfl

section Card

variable [Finite hnPR] (hQ : Nat.card hnPR ≤ 177408000)

include hQ

theorem stab_k {k : ℕ} (hk : k < 9) : chainB F 1408 (getLL CW k) (getLL CB k) (getLL CS k)
    (getLL CT k) (gRegs INVM RW (CFSG.KC.LaneChain.getL CG k))
    (CFSG.KC.LaneChain.getN hnCN k) = true := by
  have h := allRange_sound stab_ok k hk
  rw [Nat.zero_add] at h
  exact (CFSG.Certificates.TwDce2.Words.kandB_iff.1 h).2

theorem card_hnK_ge {k : ℕ} (hk : k < 9) :
    CFSG.KC.LaneChain.getN hnCN k ≤ Nat.card (hnK k) := by
  have hs := chainB_sound (G := hnPR) hnX hnPt hnPt_one hnPt_mul (fun c hc p hp => hnF_lt hc hp)
    (fun c hc p hp => hnPt_x hc hp) (hnK k)
    (fun c hc => ⟨(gens_ok k hk c hc).1, Subgroup.subset_closure ⟨c, hc, rfl⟩⟩)
    (lens_ok k hk) (stab_k hQ hk)
  have : Finite {g : hnPR // g ∈ hnK k ∧ ∀ b ∈ getLL CB k,
      hnPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} :=
    Subtype.finite
  have : Nonempty {g : hnPR // g ∈ hnK k ∧ ∀ b ∈ getLL CB k,
      hnPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} :=
    ⟨⟨1, Subgroup.one_mem _, fun b _ => hnPt_one _⟩⟩
  exact le_trans (Nat.le_mul_of_pos_right _ Nat.card_pos) hs

theorem pt_eq_one {q : hnPR} (hq : ∀ i < NB, hnPt q (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
    CFSG.KC.TwDce.fld BS (16 * i) 65535) : q = 1 := by
  have hs := chainB_sound (G := hnPR) hnX hnPt hnPt_one hnPt_mul (fun c hc p hp => hnF_lt hc hp)
    (fun c hc p hp => hnPt_x hc hp) ⊤
    (fun c hc => ⟨(gens_ok 0 (by norm_num) c hc).1, Subgroup.mem_top _⟩)
    (lens_ok 0 (by norm_num)) (stab_k hQ (k := 0) (by norm_num))
  rw [Subgroup.card_top] at hs
  have e0 : CFSG.KC.LaneChain.getN hnCN 0 = 177408000 := rfl
  rw [e0] at hs
  have : Finite {g : hnPR // g ∈ (⊤ : Subgroup hnPR) ∧ ∀ b ∈ getLL CB 0,
      hnPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} :=
    Subtype.finite
  have h1 : Nat.card {g : hnPR // g ∈ (⊤ : Subgroup hnPR) ∧ ∀ b ∈ getLL CB 0,
      hnPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} ≤ 1 := by
    omega
  have hsub := Finite.card_le_one_iff_subsingleton.1 h1
  have hmem : ∀ g : hnPR, (∀ i < NB, hnPt g (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535) → g ∈ (⊤ : Subgroup hnPR) ∧ ∀ b ∈ getLL CB 0,
        hnPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2 := by
    intro g hg
    refine ⟨Subgroup.mem_top _, fun b hb => ?_⟩
    obtain ⟨i, hi, he⟩ := base_ok.2 b hb
    rw [he]
    exact hg i hi
  exact congrArg Subtype.val (hsub.elim ⟨q, hmem q hq⟩ ⟨1, hmem 1 fun i _ => hnPt_one _⟩)

theorem hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
    (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535) → evalWord hnXP w = 1 := by
  intro w hw hfix
  rw [evalWord_hnXP, pt_eq_one hQ (q := evalWord hnX w) (fun i hi => by
    rw [hnPt_evalWord w hw (base_ok.1 i hi)]
    exact hfix i hi), map_one]

theorem orbit_zero {p : ℕ} (hp : p < 1408) : ∃ q : hnPR, hnPt q 0 = p := by
  obtain ⟨f, -, -, -, -, g, -, he⟩ := cover_pt (k := 0) (by norm_num) hp
  exact ⟨_, he.symm⟩

theorem card_hnS0_le : Nat.card hnS0 ≤ 126000 := by
  let φ : hnPR ⧸ hnS0 → Fin 1408 := fun z => Quotient.liftOn' z
    (fun a => (⟨hnPt a⁻¹ 0, hnPt_lt (by norm_num)⟩ : Fin 1408)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply Fin.ext
      change hnPt a⁻¹ 0 = hnPt b⁻¹ 0
      have e : b⁻¹ = (a⁻¹ * b)⁻¹ * a⁻¹ := by group
      rw [e, hnPt_mul, mem_hnS0.1 (hnS0.inv_mem hab)])
  have hsurj : Function.Surjective φ := by
    intro p
    obtain ⟨q, hq⟩ := orbit_zero hQ p.2
    refine ⟨((q⁻¹ : hnPR) : hnPR ⧸ hnS0), Fin.ext ?_⟩
    change hnPt q⁻¹⁻¹ 0 = p
    rw [inv_inv, hq]
  have h1 : 1408 ≤ hnS0.index := by
    rw [Subgroup.index_eq_card]
    have := Nat.card_le_card_of_surjective φ hsurj
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h2 := hnS0.card_mul_index
  by_contra h
  have h3 := Nat.mul_le_mul (Nat.succ_le_of_lt (not_le.1 h)) h1
  omega

theorem hnK1_le : hnK 1 ≤ hnS0 := by
  rw [hnK, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  change hnPt _ 0 = 0
  rw [← evP_pt (gWord_lt (isStabOf_sound (gens_ok 1 (by norm_num) c hc).2).1) (by norm_num)]
  exact node1_fix c hc

theorem hnS0_eq : hnK 1 = hnS0 := by
  have h := card_hnK_ge hQ (k := 1) (by norm_num)
  have e1 : CFSG.KC.LaneChain.getN hnCN 1 = 126000 := rfl
  rw [e1] at h
  exact Subgroup.eq_of_le_of_card_ge (hnK1_le hQ) ((card_hnS0_le hQ).trans h)

end Card

noncomputable abbrev hnT : hnPP := PresentedGroup.of 6

theorem hnXP_mem_TP {c : ℕ} (hc : c < 4) : hnXP c ∈ hnTP := by
  rw [hnXP_eq (by omega)]
  have hm : PresentedGroup.of (⟨c / 2, by omega⟩ : Fin 7) ∈ hnTP := by
    rcases (show c / 2 = 0 ∨ c / 2 = 1 by omega) with h | h
    · rw [show (⟨c / 2, by omega⟩ : Fin 7) = 0 from Fin.ext h]
      exact Subgroup.subset_closure (by simp)
    · rw [show (⟨c / 2, by omega⟩ : Fin 7) = 1 from Fin.ext h]
      exact Subgroup.subset_closure (by simp)
  split_ifs
  · exact hm
  · exact hnTP.inv_mem hm

theorem pi_S0_le [Finite hnPR] (hQ : Nat.card hnPR ≤ 177408000) {q : hnPR} (hq : q ∈ hnS0) :
    hnPi q ∈ hnTP := by
  rw [← hnS0_eq hQ] at hq
  have : (hnK 1).map hnPi ≤ hnTP := by
    rw [hnK, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, ← wVal_hnXP, wVal, evalWord]
    refine hnTP.list_prod_mem fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    exact hnXP_mem_TP (gens1_ok c hc d hd)
  exact this ⟨q, hq, rfl⟩

theorem hnTP_le : hnTP ≤ hnHP := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.subset_closure ⟨0, by decide, rfl⟩
  · exact Subgroup.subset_closure ⟨1, by decide, rfl⟩

theorem hnT_pow : hnT ^ 10 = 1 := by
  have hr : [((6 : Fin 7), true), (6, true), (6, true), (6, true), (6, true)] ∈ hnRels := by
    decide
  have h := rel_sq_PP hr
  have hv : FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus)
      (FreeGroup.mk [((6 : Fin 7), true), (6, true), (6, true), (6, true), (6, true)]) =
        hnT ^ 5 := by
    simp [FreeGroup.lift_mk, pow_succ, mul_assoc, hnT]
  rw [hv, ← pow_add] at h
  exact h

theorem hnTL_mem : ∀ j : Fin 7, j.val < 6 → j ∈ hnTL := by decide

theorem hgen : Subgroup.closure ((hnHP : Set hnPP) ∪ {hnT}) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  by_cases hj : j.val < 6
  · exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure ⟨j, hnTL_mem j hj, rfl⟩))
  · have e : j = 6 := Fin.ext (by have := j.isLt; change j.val = 6; omega)
    rw [e]
    exact Subgroup.subset_closure (Or.inr rfl)

theorem wdVal_letter {c : ℕ} (hc : c < 14) : wdVal hnXP hnT c =
    cond (decide (c % 2 = 0)) (PresentedGroup.of (⟨c / 2 % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7))
      (PresentedGroup.of (⟨c / 2 % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7))⁻¹ := by
  unfold wdVal
  by_cases h12 : c < 12
  · rw [if_pos h12, hnXP_eq h12]
    have e : (⟨c / 2 % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7) = ⟨c / 2, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [e]
    by_cases h : c % 2 = 0 <;> simp [h]
  · rw [if_neg h12]
    rcases (show c = 12 ∨ c = 13 by omega) with rfl | rfl
    · rfl
    · rfl

theorem evalWord_wd_codes : ∀ r : List ℕ, (∀ c ∈ r, c < 14) →
    evalWord (wdVal hnXP hnT) r =
      PresentedGroup.mk {r : FreeGroup (Fin 7) | r ∈ hnCoverPlus.map FreeGroup.mk}
        (FreeGroup.mk (ofCodes r)) := by
  intro r hr
  rw [CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk, evalWord, ofCodes,
    List.map_map]
  congr 1
  exact List.map_congr_left fun c hc => wdVal_letter (hr c hc)

theorem wdVal_filter : ∀ l : List ℕ,
    evalWord (wdVal hnXP hnT) l = evalWord (wdVal hnXP hnT) (l.filter (· != 14))
  | [] => rfl
  | c :: l => by
    by_cases h : c = 14
    · subst h
      rw [List.filter_cons_of_neg (by decide), evalWord_cons, ← wdVal_filter l]
      simp [wdVal]
    · rw [List.filter_cons_of_pos (by simpa using h), evalWord_cons, evalWord_cons,
        wdVal_filter l]

theorem wd_one {i : ℕ} (hi : i < 4096) : evalWord (wdVal hnXP hnT) (wList (WD i)) = 1 := by
  rw [wdVal_filter]
  rcases (wd_ok i hi).2.2 with h | h | h | ⟨r, hr, hv⟩
  · rw [h]; rfl
  · rw [h]; simp [evalWord, wdVal]
  · rw [h]; simp [evalWord, wdVal]
  · refine evalWord_rotation hv ?_
    rw [evalWord_wd_codes r (top_lt r hr)]
    refine PresentedGroup.one_of_mem (List.mem_map_of_mem ?_)
    exact mem_of_all_contains CertificateChecks.KernelHNMult.hnIncl _
      (List.mem_map_of_mem hr)

theorem foldRange_succ' (a n S : ℕ) : foldRange F INVM BS NB RD RW RA WD RJ a (n + 1) S =
    foldRange F INVM BS NB RD RW RA WD RJ (a + 1) n (foldStep F INVM BS NB RD RW RA WD RJ a S) :=
  sN_eq _ _

theorem foldRange_add' (m : ℕ) : ∀ n a S, foldRange F INVM BS NB RD RW RA WD RJ a (n + m) S =
    foldRange F INVM BS NB RD RW RA WD RJ (a + n) m (foldRange F INVM BS NB RD RW RA WD RJ a n S)
  | 0, a, S => by simp only [Nat.zero_add, Nat.add_zero]; rfl
  | n + 1, a, S => by
    rw [show n + 1 + m = (n + m) + 1 by omega, foldRange_succ', foldRange_add' m n (a + 1),
      foldRange_succ', show a + 1 + n = a + (n + 1) by omega]

theorem fold_ok : foldRange F INVM BS NB RD RW RA WD RJ 0 498 1 = 10 := by
  have h := foldRange_add' 248 250 0 1
  rw [fold0, Nat.zero_add, fold1] at h
  exact h

theorem hxH : ∀ c < 12, hnXP c ∈ hnHP := by
  intro c _
  rw [← range_hnPi]
  exact ⟨_, rfl⟩

theorem hinvP : ∀ c < 12, ivL INVM c < 12 ∧ hnXP (ivL INVM c) = (hnXP c)⁻¹ :=
  fun c hc => ⟨ivL_lt hc, hnXP_ivL hc⟩

theorem hTP : ∀ c < 4, hnXP c * hnT = hnT * hnXP c := by
  intro c hc
  have h := hnTP_conj_t (hnXP_mem_TP hc)
  calc hnXP c * hnT = hnT * (hnT⁻¹ * hnXP c * hnT) := by group
    _ = hnT * hnXP c := by rw [h]

theorem hWD : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    evalWord (wdVal hnXP hnT) (wList (WD i)) = 1 :=
  fun i hi => ⟨(wd_ok i hi).1, (wd_ok i hi).2.1, wd_one hi⟩

theorem hlenR : ∀ r < 498, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧ CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16 :=
  fun r hr => ⟨(rec_ok r hr).1, (rec_ok r hr).2.1⟩

section Index

variable [Finite hnPR] (hQ : Nat.card hnPR ≤ 177408000)

include hQ

theorem facts : ∃ X : ℕ → hnPP, X 0 = 1 ∧ ∀ r < 498, dKind (RD r) < 5 ∧ dN1 (RD r) < 10 ∧
    dN2 (RD r) < 10 ∧
    (dKind (RD r) < 3 →
      X (dN1 (RD r)) * wVal hnXP (RW r) * hnT * (X (dN2 (RD r)) * wVal hnXP (RA r))⁻¹ ∈ hnHP) ∧
    (3 ≤ dKind (RD r) → X (dN1 (RD r)) * (X (dN2 (RD r)) * wVal hnXP (RW r))⁻¹ ∈ hnHP) :=
  CFSG.Certificates.TwDce2.dce_sound fold_ok (by norm_num) hnHP hnXP hnT hxH hinvP hTP hWD (hone hQ)
    hlenR

theorem relIndex_map_hnPi_le (P : Subgroup hnPR) : (P.map hnPi).relIndex hnPi.range ≤ P.index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le le_sup_left)

theorem cn_pos : ∀ k < 9, 0 < CFSG.KC.LaneChain.getN hnCN k := by decide

theorem idx_le (i : Fin 9) :
    ((hnSt i).map hnPi).relIndex hnHP ≤ 177408000 / CFSG.KC.LaneChain.getN hnCN i := by
  rw [← range_hnPi]
  refine (relIndex_map_hnPi_le hQ (hnSt i)).trans ?_
  rw [Nat.le_div_iff_mul_le (cn_pos hQ i i.2)]
  have h1 := (card_hnK_ge hQ i.2).trans (Subgroup.card_le_of_le (hnK_le_hnSt i.2))
  calc (hnSt i).index * CFSG.KC.LaneChain.getN hnCN i ≤ (hnSt i).index * Nat.card (hnSt i) :=
        Nat.mul_le_mul_left _ h1
    _ = Nat.card hnPR := (hnSt i).index_mul_card
    _ ≤ 177408000 := hQ

theorem index_hnHP_le : hnHP.FiniteIndex ∧ hnHP.index ≤ 1539000 := by
  classical
  obtain ⟨X, hX0, hX⟩ := facts hQ
  have hwH : ∀ w, (∀ c ∈ wList w, c < 12) → wVal hnXP w ∈ hnHP := by
    intro w _
    rw [wVal_hnXP, ← range_hnPi]
    exact ⟨_, rfl⟩
  let repS : Fin 9 → Set hnPP := fun i => {k | ∃ f < 498, dKind (RD f) < 3 ∧ dN1 (RD f) = i ∧
    dN2 (RD f) < 9 ∧ k = wVal hnXP (RW f)}
  let tP : Fin 9 → hnPP → Prop := fun i k =>
    ∃ j : Fin 9, ∃ v, v ∈ hnHP ∧ X i * k * hnT * (X j * v)⁻¹ ∈ hnHP
  have htP : ∀ i : Fin 9, ∀ k ∈ repS i, tP i k := by
    rintro i _ ⟨f, hf, hk, hn1, hn2, rfl⟩
    have hfa := (hX f hf).2.2.2.1 hk
    refine ⟨⟨_, hn2⟩, wVal hnXP (RA f), hwH _ (rec_ok f hf).2.2.2.1, ?_⟩
    rw [← hn1]
    exact hfa
  let D : TwistData hnHP hnTP hnT 9 :=
    { x := fun i => X i
      S := fun i => (hnSt i).map hnPi
      rep := repS
      tgt := fun i k => if h : tP i k then h.choose else 0
      tgtElt := fun i k => if h : tP i k then h.choose_spec.choose else 1
      base := 0
      base_mem := by
        change X 0 ∈ hnHP
        rw [hX0]
        exact hnHP.one_mem
      S_le := fun i => by
        rw [← range_hnPi]
        exact Subgroup.map_le_range _ _
      S_conj := by
        rintro i _ ⟨q, hq, rfl⟩
        induction hq using Subgroup.closure_induction with
        | mem q hq =>
          obtain ⟨c, hc, rfl⟩ := hq
          obtain ⟨hg, hk3, -, hn1, hn2⟩ := isStabOf_sound hc
          have hf := (hX (c / 2) hg).2.2.2.2 hk3
          rw [hn1, hn2] at hf
          rw [← wVal_hnXP, wVal_gWord (fun c hc => hnXP_ivL hc) hg]
          split_ifs
          · convert hf using 1
            group
          · convert hnHP.inv_mem hf using 1
            group
        | one => rw [map_one, mul_one, mul_inv_cancel]; exact hnHP.one_mem
        | mul a b _ _ ha hb =>
          have e : X i * hnPi (a * b) * (X i)⁻¹ =
              (X i * hnPi a * (X i)⁻¹) * (X i * hnPi b * (X i)⁻¹) := by
            rw [map_mul]; group
          rw [e]
          exact hnHP.mul_mem ha hb
        | inv a _ ha =>
          have e : X i * hnPi a⁻¹ * (X i)⁻¹ = (X i * hnPi a * (X i)⁻¹)⁻¹ := by
            rw [map_inv]; group
          rw [e]
          exact hnHP.inv_mem ha
      rep_le := by
        rintro i _ ⟨f, hf, -, -, -, rfl⟩
        exact hwH _ (rec_ok f hf).2.2.1
      rep_cover := by
        intro i h hh
        rw [← range_hnPi] at hh
        obtain ⟨q, rfl⟩ := hh
        obtain ⟨f, hf, hk, hn1, hn2, g, hg, hp⟩ :=
          cover_pt i.2 (hnPt_lt (g := q⁻¹) (p := 0) (by norm_num))
        have hc : (wVal hnX (RW f))⁻¹ * g * q ∈ hnS0 := by
          rw [mem_hnS0, hnPt_mul, ← hp, ← hnPt_mul, inv_mul_cancel, hnPt_one]
        refine ⟨wVal hnXP (RW f), ⟨f, hf, hk, hn1, hn2, rfl⟩, hnPi g⁻¹,
          ⟨g⁻¹, (hnSt i).inv_mem hg, rfl⟩, hnPi ((wVal hnX (RW f))⁻¹ * g * q), pi_S0_le hQ hc, ?_⟩
        rw [wVal_hnXP, ← map_mul, ← map_mul]
        congr 1
        group
      tgtElt_mem := by
        intro i k hk
        have h := htP i k hk
        simp only [dif_pos h]
        exact h.choose_spec.choose_spec.1
      tgt_spec := by
        intro i k hk
        have h := htP i k hk
        simp only [dif_pos h]
        exact h.choose_spec.choose_spec.2 }
  have : Finite hnHP := by
    rw [← range_hnPi]
    exact Finite.of_surjective _ hnPi.rangeRestrict_surjective
  obtain ⟨hfi, hle⟩ := D.index_le_sum_of_pow (n := 10) (by norm_num) hnT_pow
    (fun c hc => by rw [hnTP_conj_t hc]; exact hnTP_le hc) hgen
  refine ⟨hfi, hle.trans ?_⟩
  calc ∑ i, (D.S i).relIndex hnHP ≤ ∑ i : Fin 9, 177408000 / CFSG.KC.LaneChain.getN hnCN i :=
        Finset.sum_le_sum fun i _ => idx_le hQ i
    _ = 1539000 := cn_sum

theorem card_PC_le_of_card (hinj : Function.Injective (hnPsi CertificateChecks.KernelHNMult.hnGens_gf)) :
    Finite PC ∧ Nat.card PC ≤ 273030912000000 := by
  obtain ⟨hfi, hidx⟩ := index_hnHP_le hQ
  have : Finite hnHP := by
    rw [← range_hnPi]
    exact Finite.of_surjective _ hnPi.rangeRestrict_surjective
  have hH : Nat.card hnHP ≤ 177408000 := by
    rw [← range_hnPi]
    exact (Nat.card_le_card_of_surjective _ hnPi.rangeRestrict_surjective).trans hQ
  have : Finite (hnPP ⧸ hnHP) := Subgroup.finite_quotient_of_finiteIndex
  have hf : Finite hnPP := Finite.of_subgroup_quotient hnHP
  have hle : Nat.card hnPP ≤ 273030912000000 := by
    rw [← hnHP.index_mul_card]
    calc hnHP.index * Nat.card hnHP ≤ 1539000 * 177408000 := Nat.mul_le_mul hidx hH
      _ = 273030912000000 := by norm_num
  have hextra : ∀ w ∈ hnCoverPlus, FreeGroup.lift hx (FreeGroup.mk w) = 1 := by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact lift_coverGen_eq_one w hw
    · rcases List.mem_append.1 hw with hw | hw
      · exact hnPlain1_eval CertificateChecks.KernelHNMult.hnGens_gf hinj w hw
      · exact hnNwords_eval CertificateChecks.KernelHNMult.hnGens_gf hinj w hw
  let π' : hnPP →* PC := PresentedGroup.toGroup (f := hx) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hextra w hw
  have hsurj : Function.Surjective π' := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  exact ⟨Finite.of_surjective π' hsurj, (Nat.card_le_card_of_surjective π' hsurj).trans hle⟩

end Index

end CFSG.KD.HNDce2

end
