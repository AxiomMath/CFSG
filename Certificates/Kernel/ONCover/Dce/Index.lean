module

public import Certificates.Kernel.ONCover.Dce.Ident
public import Certificates.Kernel.ONCover.Dce.Below
public import Certificates.Kernel.ONCover.Dce.Cover0
public import Certificates.Kernel.ONCover.Dce.Cover1
public import Certificates.Kernel.ONCover.Dce.Cover2
public import Certificates.Kernel.ONCover.Dce.Cover3
public import Certificates.Kernel.ONCover.Dce.Cover4
public import Certificates.Kernel.ONCover.Dce.Cover5
public import Certificates.Kernel.ONCover.Dce.Cover6
public import Certificates.Kernel.ONCover.Dce.Cover7
public import Certificates.Kernel.ONCover.Dce.Cover8
public import Certificates.Kernel.ONCover.Dce.CoverRels
public import CFSG.Certificates.Kernel.TwistDce3.CoverSaltSound
public import CFSG.Certificates.Kernel.TwistDce2.IndexFinite
public import CFSG.Certificates.Kernel.TwistDce3.Sound

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce2 CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier
  CFSG.LieType.Multipliers CFSG.Certificates.CosetEnumeration CFSG.KC.YModel
  CFSG.Certificates.TwDce CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover
open CFSG.Certificates.TwDce2 (chainB_sound chainLens)
open CertificateChecks.KernelONCover (card_mainWs₁_le)

theorem hcodes_len : ∀ w ∈ onHCodes, w.length < 2 ^ 32 := by
  decide +kernel

theorem id_hcodes : ∀ c < 12, 6 ≤ c → [c] ∈ onHCodes := by
  decide +kernel

theorem q_shape : ∀ w ∈ onQCodes, w.map onSw ∈ onHCodes ∨
    ∃ a < 6, ∃ r ∈ onHCodes, w.map onSw = a :: (r ++ Nat.xor a 1 :: invCodes r) := by
  decide +kernel

theorem sw_ok : ∀ j < 3, onSw (2 * j) < 6 ∧ onSw (2 * j + 1) = ivL INVM (onSw (2 * j)) := by
  decide +kernel

theorem xor_ok : ∀ c < 12, Nat.xor c 1 < 12 ∧ (c < 6 → Nat.xor c 1 = ivL INVM c) ∧
    (6 ≤ c → 6 ≤ Nat.xor c 1) := by
  decide +kernel

theorem gens_all : ∀ i < 15, ∀ c ∈ CFSG.KC.LaneChain.getL CG i,
    wBelow 12 (gWord INVM RW c) = true := by
  decide +kernel

theorem lens_all : ∀ i < 15, ∀ m ∈ chainLens ((gRegs INVM RW (CFSG.KC.LaneChain.getL CG i)).map
    fun r => CFSG.KC.TwDce.wLen (r / 2)) (getLL CW i), m < 2 ^ 32 := by
  decide +kernel

theorem node1_fix : ∀ c ∈ CFSG.KC.LaneChain.getL CG 1,
    CFSG.KC.TwDce3.evP 14 FO (gWord INVM RW c) 0 = 0 := by
  decide +kernel

theorem gens1_ok : ∀ c ∈ CFSG.KC.LaneChain.getL CG 1, ∀ d ∈ wList (gWord INVM RW c),
    d < 4 ∨ 6 ≤ d := by
  decide +kernel

theorem ds_mem : ∀ n ∈ DS, ∃ j : Fin 15, CFSG.KC.LaneChain.getN DS j = n := by
  rw [ds_eq.1]
  decide

theorem ds_zero : CFSG.KC.LaneChain.getN DS 0 = 0 := by
  rw [ds_eq.1]
  rfl

theorem cn_pos : ∀ i < 15, 0 < CFSG.KC.LaneChain.getN CN i := by
  rw [ds_eq.2]
  decide

theorem cn_one : CFSG.KC.LaneChain.getN CN 1 = 168 := by
  rw [ds_eq.2]
  rfl

theorem cn_sum : ∑ i : Fin 15, 1876896 / CFSG.KC.LaneChain.getN CN i = 736560 := by
  rw [ds_eq.2]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  decide

theorem ivl_lt {c : ℕ} (hc : c < 12) : ivL INVM c < 12 :=
  (CFSG.Certificates.TwDce3.lettersOK_sound letters_ok c hc).1

theorem fo_lt : ∀ c < 12, ∀ p < 11172, fieldAt 14 (FO c) p < 11172 :=
  fun c hc p hp => ((CFSG.Certificates.TwDce3.lettersOK_sound letters_ok c hc).2 p hp).1

theorem fo_inv : ∀ c < 12, ∀ p < 11172,
    fieldAt 14 (FO (ivL INVM c)) (fieldAt 14 (FO c) p) = p :=
  fun c hc p hp => ((CFSG.Certificates.TwDce3.lettersOK_sound letters_ok c hc).2 p hp).2

@[expose] noncomputable def foldO (w : List ℕ) (p : ℕ) : ℕ := w.foldl (fun q c => fieldAt 14 (FO c) q) p

theorem foldO_cons (c : ℕ) (w : List ℕ) (p : ℕ) :
    foldO (c :: w) p = foldO w (fieldAt 14 (FO c) p) := rfl

theorem foldO_append (u v : List ℕ) (p : ℕ) : foldO (u ++ v) p = foldO v (foldO u p) :=
  List.foldl_append

theorem hcodes_fix : ∀ w ∈ onHCodes, (∀ c ∈ w, c < 12) ∧ ∀ p < 11172, foldO w p = p :=
  CFSG.Certificates.TwDce3.relsOK_sound rels_ok hcodes_len

theorem fo_id {c : ℕ} (hc : c < 12) (h6 : 6 ≤ c) {p : ℕ} (hp : p < 11172) :
    fieldAt 14 (FO c) p = p :=
  (hcodes_fix [c] (id_hcodes c hc h6)).2 p hp

theorem fo_xor {c : ℕ} (hc : c < 12) {p : ℕ} (hp : p < 11172) :
    fieldAt 14 (FO (Nat.xor c 1)) (fieldAt 14 (FO c) p) = p := by
  obtain ⟨hx, h1, h2⟩ := xor_ok c hc
  by_cases h6 : c < 6
  · rw [h1 h6]
    exact fo_inv c hc p hp
  · rw [fo_id hc (by omega) hp, fo_id hx (h2 (by omega)) hp]

theorem foldO_inv : ∀ w : List ℕ, (∀ c ∈ w, c < 12) → ∀ p < 11172,
    foldO (invCodes w) (foldO w p) = p
  | [], _, _, _ => rfl
  | c :: w, hw, p, hp => by
    have hc := hw c List.mem_cons_self
    have hw' : ∀ d ∈ w, d < 12 := fun d hd => hw d (List.mem_cons_of_mem _ hd)
    have e : invCodes (c :: w) = invCodes w ++ [Nat.xor c 1] := by
      simp [invCodes]
    rw [e, foldO_append, foldO_cons c w p, foldO_inv w hw' _ (fo_lt c hc p hp)]
    exact fo_xor hc hp

theorem foldO_inv_fix {w : List ℕ} (hw : ∀ c ∈ w, c < 12) (hf : ∀ p < 11172, foldO w p = p)
    {p : ℕ} (hp : p < 11172) : foldO (invCodes w) p = p := by
  have h := foldO_inv w hw p hp
  rwa [hf p hp] at h

theorem shape_fix {w : List ℕ} (hw : w ∈ onQCodes) {p : ℕ} (hp : p < 11172) :
    foldO (w.map onSw) p = p := by
  rcases q_shape w hw with h | ⟨a, ha, r, hr, e⟩
  · exact (hcodes_fix _ h).2 p hp
  · obtain ⟨hl, hf⟩ := hcodes_fix r hr
    have ha' : a < 12 := by omega
    rw [e, foldO_cons, foldO_append, hf _ (fo_lt a ha' p hp), foldO_cons, fo_xor ha' hp]
    exact foldO_inv_fix hl hf hp

@[expose] noncomputable def permO (c : ℕ) (hc : c < 12) : Equiv.Perm (Fin 11172) where
  toFun p := ⟨fieldAt 14 (FO c) p, fo_lt c hc p p.2⟩
  invFun p := ⟨fieldAt 14 (FO (ivL INVM c)) p, fo_lt _ (ivl_lt hc) p p.2⟩
  left_inv p := Fin.ext (fo_inv c hc p p.2)
  right_inv q := by
    have hinj : Function.Injective (fun p : Fin 11172 =>
        (⟨fieldAt 14 (FO c) p, fo_lt c hc p p.2⟩ : Fin 11172)) := by
      intro p p' e
      have e' := congrArg (fun r : Fin 11172 => fieldAt 14 (FO (ivL INVM c)) r.val) e
      simp only at e'
      rw [fo_inv c hc p p.2, fo_inv c hc p' p'.2] at e'
      exact Fin.ext e'
    obtain ⟨p, rfl⟩ := Finite.injective_iff_surjective.1 hinj q
    exact Fin.ext (congrArg (fieldAt 14 (FO c)) (fo_inv c hc p p.2))

@[expose] noncomputable def genO (j : ℕ) : (Equiv.Perm (Fin 11172))ᵐᵒᵖ :=
  if h : j < 3 then MulOpposite.op (permO (onSw (2 * j)) (by have := (sw_ok j h).1; omega))
  else 1

theorem genO_apply {j : ℕ} (hj : j < 3) (p : Fin 11172) :
    ((genO j).unop p).val = fieldAt 14 (FO (onSw (2 * j))) p.val := by
  rw [genO, dif_pos hj]
  rfl

theorem genO_inv_apply {j : ℕ} (hj : j < 3) (p : Fin 11172) :
    ((genO j)⁻¹.unop p).val = fieldAt 14 (FO (onSw (2 * j + 1))) p.val := by
  rw [genO, dif_pos hj, MulOpposite.unop_inv, MulOpposite.unop_op, Equiv.Perm.inv_def,
    (sw_ok j hj).2]
  rfl

theorem liftO_mk_apply : ∀ (u : List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) (p : Fin 11172),
    ((FreeGroup.lift (fun j => genO j.val) (FreeGroup.mk u)).unop p).val =
      foldO ((u.map CFSG.Certificates.TwDce2.Rels.letterCode).map onSw) p.val
  | [], _ => rfl
  | l :: u, p => by
    have e : FreeGroup.mk (l :: u) = FreeGroup.mk [l] * FreeGroup.mk u := by
      rw [FreeGroup.mul_mk]
      rfl
    rw [e, map_mul, MulOpposite.unop_mul, Equiv.Perm.mul_apply, liftO_mk_apply u, List.map_cons,
      List.map_cons, foldO_cons]
    congr 1
    have hl : l.1.val < 3 := Nat.lt_of_lt_of_eq l.1.isLt onS_length
    rw [FreeGroup.lift_mk]
    rcases l with ⟨j, _ | _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, cond_false]
      rw [genO_inv_apply hl]
      rfl
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, cond_true]
      rw [genO_apply hl]
      rfl

theorem relO {r : List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)} (hr : r ∈ mainWs₁) :
    FreeGroup.lift (fun j => genO j.val) (FreeGroup.mk r) = 1 := by
  have hr' : r ∈ CertificateChecks.KernelONCover.mainWs₁U :=
    CertificateChecks.KernelONCover.mainWs₁_perm.mem_iff.1 hr
  have hc : r.map CFSG.Certificates.TwDce2.Rels.letterCode ∈ onQCodes :=
    List.mem_map.2 ⟨r, hr', rfl⟩
  apply MulOpposite.unop_injective
  ext p
  rw [liftO_mk_apply r p, shape_fix hc p.2]
  rfl

@[expose] noncomputable def onRhoO : onQ →* (Equiv.Perm (Fin 11172))ᵐᵒᵖ :=
  PresentedGroup.toGroup (f := fun j => genO j.val) (by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact relO hr)

@[expose] noncomputable def onPtO (q : onQ) (p : ℕ) : ℕ :=
  if h : p < 11172 then ((onRhoO q).unop ⟨p, h⟩).val else p

theorem onPtO_of_lt (q : onQ) {p : ℕ} (hp : p < 11172) :
    onPtO q p = ((onRhoO q).unop ⟨p, hp⟩).val :=
  dif_pos hp

theorem onPtO_lt (q : onQ) {p : ℕ} (hp : p < 11172) : onPtO q p < 11172 := by
  rw [onPtO_of_lt _ hp]
  exact Fin.isLt _

theorem onPtO_one (p : ℕ) : onPtO 1 p = p := by
  by_cases h : p < 11172
  · rw [onPtO_of_lt _ h, map_one]
    rfl
  · exact dif_neg h

theorem onPtO_mul (a b : onQ) (p : ℕ) : onPtO (a * b) p = onPtO b (onPtO a p) := by
  by_cases h : p < 11172
  · rw [onPtO_of_lt _ h, onPtO_of_lt a h, onPtO_of_lt _ (Fin.isLt _), map_mul,
      MulOpposite.unop_mul, Equiv.Perm.mul_apply]
  · simp [onPtO, h]

theorem ptO_of (j : Fin (subsetOf 4 [0, 1, 2]).length) {p : ℕ} (hp : p < 11172) :
    onPtO (PresentedGroup.of j) p = fieldAt 14 (FO (onSw (2 * j.val))) p := by
  rw [onPtO_of_lt _ hp, onRhoO, PresentedGroup.toGroup.of]
  exact genO_apply (Nat.lt_of_lt_of_eq j.isLt onS_length) ⟨p, hp⟩

theorem ptO_of_inv (j : Fin (subsetOf 4 [0, 1, 2]).length) {p : ℕ} (hp : p < 11172) :
    onPtO (PresentedGroup.of j)⁻¹ p = fieldAt 14 (FO (onSw (2 * j.val + 1))) p := by
  rw [onPtO_of_lt _ hp, map_inv, onRhoO, PresentedGroup.toGroup.of]
  exact genO_inv_apply (Nat.lt_of_lt_of_eq j.isLt onS_length) ⟨p, hp⟩

theorem hxO : ∀ c < 12, ∀ p < 11172, fieldAt 14 (FO c) p = onPtO (xD c) p := by
  intro c hc p hp
  by_cases h6 : c < 6
  · have e := hsw c h6
    rw [xD, if_pos h6]
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · rw [if_pos h, ptO_of _ hp]
      rw [h, Nat.add_zero] at e
      rw [e]
    · rw [if_neg (by omega), ptO_of_inv _ hp]
      rw [h] at e
      rw [e]
  · rw [xD, if_neg h6, onPtO_one, fo_id hc (by omega) hp]

theorem ptO_eval : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → ∀ p < 11172,
    onPtO (evalWord xD w) p = foldO w p
  | [], _, p, _ => onPtO_one p
  | c :: w, hw, p, hp => by
    have hc := hw c List.mem_cons_self
    rw [evalWord_cons, onPtO_mul, ← hxO c hc p hp, foldO_cons]
    exact ptO_eval w (fun d hd => hw d (List.mem_cons_of_mem _ hd)) _ (fo_lt c hc p hp)

theorem evP_O {w : ℕ} (hw : ∀ c ∈ wList w, c < 12) {p : ℕ} (hp : p < 11172) :
    CFSG.KC.TwDce3.evP 14 FO w p = onPtO (wVal xD w) p := by
  rw [CFSG.Certificates.TwDce3.Words.evP_eq, wVal, ptO_eval _ hw p hp]
  rfl

theorem rw_lt {r : ℕ} (hr : r < 18934) : ∀ c ∈ wList (RW r), c < 12 :=
  fun c hc => (CFSG.Certificates.TwDce2.Words.wBelow_spec (rw_below r hr)).2 c hc

theorem gWord_eq (c : ℕ) :
    gWord INVM RW c = if c % 2 = 1 then wInv INVM (RW (c / 2)) else RW (c / 2) := by
  unfold gWord
  have h0 : Nat.shiftRight c 1 = c >>> 1 := rfl
  have h1 : Nat.shiftRight c 1 = c / 2 := by
    rw [h0, Nat.shiftRight_eq_div_pow]
  have h2 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h, if_neg (by norm_num)]
    rfl
  · rw [h, if_pos rfl]
    rfl

theorem wInv_lt {w : ℕ} (hw : ∀ c ∈ wList w, c < 12) : ∀ c ∈ wList (wInv INVM w), c < 12 := by
  intro c hc
  have e : wList (wInv INVM w) = (wList w).reverse.map (ivL INVM) :=
    (CFSG.Certificates.TwDce2.Words.wInv_spec INVM w).2.2
  rw [e] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact ivl_lt (hw d (List.mem_reverse.1 hd))

theorem gWord_lt {c : ℕ} (hc : c / 2 < 18934) : ∀ d ∈ wList (gWord INVM RW c), d < 12 := by
  rw [gWord_eq]
  split_ifs
  · exact wInv_lt (rw_lt hc)
  · exact rw_lt hc

theorem evalWord_rev_inv {G : Type*} [Group G] {y : ℕ → G} :
    ∀ {l : List ℕ}, (∀ c ∈ l, y (ivL INVM c) = (y c)⁻¹) →
      evalWord y ((l.reverse).map (ivL INVM)) = (evalWord y l)⁻¹
  | [], _ => by simp [evalWord]
  | c :: l, h => by
    have ih := evalWord_rev_inv (y := y) (l := l) fun d hd => h d (List.mem_cons_of_mem _ hd)
    simp only [evalWord, List.map_map] at ih ⊢
    rw [List.reverse_cons, List.map_append, List.prod_append, ih]
    simp [h c List.mem_cons_self]

theorem wVal_wInv {G : Type*} [Group G] {y : ℕ → G} (hy : ∀ c < 12, y (ivL INVM c) = (y c)⁻¹)
    {w : ℕ} (hw : ∀ c ∈ wList w, c < 12) : wVal y (wInv INVM w) = (wVal y w)⁻¹ := by
  have e : wList (wInv INVM w) = (wList w).reverse.map (ivL INVM) :=
    (CFSG.Certificates.TwDce2.Words.wInv_spec INVM w).2.2
  rw [wVal, e, evalWord_rev_inv fun c hc => hy c (hw c hc)]
  rfl

theorem wVal_gWord {G : Type*} [Group G] {y : ℕ → G} (hy : ∀ c < 12, y (ivL INVM c) = (y c)⁻¹)
    {c : ℕ} (hc : c / 2 < 18934) : wVal y (gWord INVM RW c) =
      if c % 2 = 1 then (wVal y (RW (c / 2)))⁻¹ else wVal y (RW (c / 2)) := by
  rw [gWord_eq]
  split_ifs
  · exact wVal_wInv hy (rw_lt hc)
  · rfl

theorem hinvX : ∀ c < 12, onX (ivL INVM c) = (onX c)⁻¹ := fun c hc => (hinv c hc).2

theorem onQGen_congr {d e : ℕ} (h : d / 2 = e / 2) : onQGen d = onQGen e := by
  simp only [onQGen, h]

theorem xD_ivL {c : ℕ} (hc : c < 12) : xD (ivL INVM c) = (xD c)⁻¹ := by
  rw [inv_eq c hc]
  by_cases h6 : c < 6
  · rw [if_pos h6]
    by_cases h : c % 2 = 0
    · rw [if_pos h]
      simp only [xD, if_pos h6, if_pos (by omega : c + 1 < 6), if_pos h,
        if_neg (by omega : ¬ (c + 1) % 2 = 0), onQGen_congr (by omega : (c + 1) / 2 = c / 2)]
    · rw [if_neg h]
      simp only [xD, if_pos h6, if_pos (by omega : c - 1 < 6), if_neg h,
        if_pos (by omega : (c - 1) % 2 = 0), inv_inv,
        onQGen_congr (by omega : (c - 1) / 2 = c / 2)]
  · rw [if_neg h6]
    simp [xD, h6]

theorem isStabOf_sound {n k g : ℕ} (h : isStabOf RD n k g = true) :
    g < n ∧ 3 ≤ dKind (RD g) ∧ dKind (RD g) < 5 ∧ dN1 (RD g) = k ∧ dN2 (RD g) = k := by
  unfold isStabOf isEq at h
  simp only [CFSG.Certificates.TwDce2.Words.kandB_iff, CFSG.Certificates.TwDce.Words.andB_iff,
    Nat.blt_eq, Nat.ble_eq, CFSG.Certificates.TwDce.Words.sB_eq] at h
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5⟩ := h
  exact ⟨h1, h2, h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem allStab_sound {k : ℕ} : ∀ {L : List ℕ}, (List.rec (motive := fun _ => Bool) true
    (fun c _ ih => CFSG.KC.andB (isStabOf RD 18934 k (Nat.shiftRight c 1)) ih) L) = true →
    ∀ c ∈ L, isStabOf RD 18934 k (c / 2) = true
  | [], _, _, hc => absurd hc List.not_mem_nil
  | c :: L, h, d, hd => by
    have h' := CFSG.Certificates.TwDce2.Words.kandB_iff.1 h
    rcases List.mem_cons.1 hd with rfl | hd
    · have e0 : Nat.shiftRight d 1 = d >>> 1 := rfl
      have e : Nat.shiftRight d 1 = d / 2 := by
        rw [e0, Nat.shiftRight_eq_div_pow, pow_one]
      rw [← e]
      exact h'.1
    · exact allStab_sound h'.2 d hd

@[expose] noncomputable def onHP : Subgroup onPC :=
  Subgroup.closure {PresentedGroup.of 0, PresentedGroup.of 1, PresentedGroup.of 2}

theorem of0_mem : (PresentedGroup.of 0 : onPC) ∈ onHP :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem of1_mem : (PresentedGroup.of 1 : onPC) ∈ onHP :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem of2_mem : (PresentedGroup.of 2 : onPC) ∈ onHP :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem onX_mem (c : ℕ) : onX c ∈ onHP := by
  by_cases h6 : c < 6
  · have hm : (PresentedGroup.of (onHGen c) : onPC) ∈ onHP := by
      rcases hgen_lt c h6 with e | e | e <;> rw [e]
      · exact of0_mem
      · exact of1_mem
      · exact of2_mem
    rw [onX, if_pos h6]
    split_ifs
    · exact hm
    · exact onHP.inv_mem hm
  · rw [onX, if_neg h6]
    exact onHP.one_mem

theorem factsP : ∃ X : ℕ → onPC, X 0 = 1 ∧ ∀ r < 18934, dKind (RD r) < 5 ∧ dN1 (RD r) < 775 ∧
    dN2 (RD r) < 775 ∧
    (dKind (RD r) < 3 →
      X (dN1 (RD r)) * wVal onX (RW r) * onT * (X (dN2 (RD r)) * wVal onX (RA r))⁻¹ ∈ onHP) ∧
    (3 ≤ dKind (RD r) → X (dN1 (RD r)) * (X (dN2 (RD r)) * wVal onX (RW r))⁻¹ ∈ onHP) := by
  have hf := fold_ok
  rw [psf_eq, psb_eq] at hf
  exact CFSG.Certificates.TwDce3.dce_sound_comm hf (by norm_num) onHP onX onT
    (fun c _ => onX_mem c) hinv (by rw [nt_eq]; norm_num)
    (fun c hc => hT c (by rw [nt_eq] at hc; exact hc)) hWD hone hlenR

theorem of_eq_xD : ∀ j : Fin (subsetOf 4 [0, 1, 2]).length,
    (PresentedGroup.of j : onQ) = xD (2 * [0, 2, 1].getD j.val 0) := by
  rintro ⟨j, hj⟩
  have hj3 : j < 3 := Nat.lt_of_lt_of_eq hj onS_length
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl <;> simp [xD, onQGen]

theorem range_onPi : onPi.range = onHP := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, of_eq_xD j, onPi_xD]
    exact onX_mem _
  · rw [onHP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨xD 0, onPi_xD 0⟩
    · exact ⟨xD 4, onPi_xD 4⟩
    · exact ⟨xD 2, onPi_xD 2⟩

theorem wVal_mem (w : ℕ) : wVal onX w ∈ onHP := by
  rw [wVal, evalWord]
  exact onHP.list_prod_mem fun y hy => by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hy
    exact onX_mem d

theorem wVal_onPi (w : ℕ) : wVal onX w = onPi (wVal xD w) := evalWord_onX _

@[expose] noncomputable def onC : Subgroup onPC := Subgroup.closure {onU, onY}

theorem onU_memC : onU ∈ onC := Subgroup.subset_closure (by simp)

theorem onY_memC : onY ∈ onC := Subgroup.subset_closure (by simp)

theorem onC_le : onC ≤ onHP := by
  rw [onC, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact onX_mem 0
  · exact onX_mem 2

theorem onC_conj {c : onPC} (hc : c ∈ onC) : onT⁻¹ * c * onT = c := by
  have hu : onU * onT = onT * onU := hT 0 (by norm_num)
  have hy : onY * onT = onT * onY := hT 2 (by norm_num)
  have hZ : onC ≤ Subgroup.centralizer {onT} := by
    rw [onC, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hu
    · exact Subgroup.mem_centralizer_singleton_iff.2 hy
  have h := Subgroup.mem_centralizer_singleton_iff.1 (hZ hc)
  rw [mul_assoc, h, inv_mul_cancel_left]

theorem onX_memC {d : ℕ} (h : d < 4 ∨ 6 ≤ d) : onX d ∈ onC := by
  rcases h with h | h
  · have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hd with rfl | rfl | rfl | rfl
    · exact onU_memC
    · exact onC.inv_mem onU_memC
    · exact onY_memC
    · exact onC.inv_mem onY_memC
  · rw [onX, if_neg (by omega)]
    exact onC.one_mem

theorem hgen : Subgroup.closure ((onHP : Set onPC) ∪ {onT}) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨⟨j, hj⟩, rfl⟩
  have hsub : (onHP : Set onPC) ⊆ Subgroup.closure ((onHP : Set onPC) ∪ {onT}) :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj4 with rfl | rfl | rfl | rfl
  · exact hsub of0_mem
  · exact hsub of1_mem
  · exact hsub of2_mem
  · exact Subgroup.subset_closure (Or.inr rfl)

@[expose] noncomputable def onSt (k : ℕ) : Subgroup onQ :=
  Subgroup.closure {q | ∃ c, isStabOf RD 18934 k (c / 2) = true ∧ q = wVal xD (gWord INVM RW c)}

@[expose] noncomputable def onK (i : ℕ) : Subgroup onQ :=
  Subgroup.closure {q | ∃ c ∈ CFSG.KC.LaneChain.getL CG i, q = wVal xD (gWord INVM RW c)}

theorem stab_i {i : ℕ} (hi : i < 15) : stabOK FB INVM 57 RD RW 18934
    (CFSG.KC.LaneChain.getN DS i) (CFSG.KC.LaneChain.getL CG i) (getLL CW i) (getLL CB i)
    (getLL CS i) (getLL CT i) (CFSG.KC.LaneChain.getN CN i) = true := by
  have h := CFSG.Certificates.TwDce3.stabRange_sound stab_ok i hi
  rwa [Nat.zero_add] at h

theorem onK_le_onSt {i : ℕ} (hi : i < 15) : onK i ≤ onSt (CFSG.KC.LaneChain.getN DS i) := by
  rw [onK, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  exact Subgroup.subset_closure
    ⟨c, allStab_sound (CFSG.Certificates.TwDce2.Words.kandB_iff.1 (stab_i hi)).1 c hc, rfl⟩

theorem card_onK_ge {i : ℕ} (hi : i < 15) :
    CFSG.KC.LaneChain.getN CN i ≤ Nat.card (onK i) := by
  have hs := chainB_sound (G := onQ) xD onPt onPt_one onPt_mul lt_ok hxD (onK i)
    (fun c hc => ⟨gens_all i hi c hc, Subgroup.subset_closure ⟨c, hc, rfl⟩⟩)
    (lens_all i hi) (CFSG.Certificates.TwDce2.Words.kandB_iff.1 (stab_i hi)).2
  have : Finite {g : onQ // g ∈ onK i ∧ ∀ b ∈ getLL CB i,
      onPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} :=
    Subtype.finite
  have : Nonempty {g : onQ // g ∈ onK i ∧ ∀ b ∈ getLL CB i,
      onPt g (CFSG.KC.LaneChain.colDat 11 b / 2) = CFSG.KC.LaneChain.colDat 11 b / 2} :=
    ⟨⟨1, Subgroup.one_mem _, fun b _ => onPt_one _⟩⟩
  exact le_trans (Nat.le_mul_of_pos_right _ Nat.card_pos) hs

theorem fold_pt {k : ℕ} : ∀ (cs : List ℕ), (∀ c ∈ cs, isStabOf RD 18934 k (c / 2) = true) →
    ∀ a : onQ, ∃ g ∈ onSt k,
      cs.foldl (fun q c => CFSG.KC.TwDce3.evP 14 FO (gWord INVM RW c) q) (onPtO a 0) =
        onPtO (a * g) 0
  | [], _, a => ⟨1, Subgroup.one_mem _, by rw [mul_one]; rfl⟩
  | c :: cs, h, a => by
    have hc := h c List.mem_cons_self
    have hc2 := (isStabOf_sound hc).1
    obtain ⟨g, hg, he⟩ := fold_pt cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      (a * wVal xD (gWord INVM RW c))
    refine ⟨wVal xD (gWord INVM RW c) * g,
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c, hc, rfl⟩) hg, ?_⟩
    rw [List.foldl_cons, evP_O (gWord_lt hc2) (onPtO_lt _ (by norm_num)), ← onPtO_mul, he,
      mul_assoc]

theorem reached {i : ℕ} (hi : i < 15) : ∀ p < 11172,
    CFSG.Certificates.TwDce3.Reached 14 FO INVM RD RW 18934 DS (CFSG.KC.LaneChain.getN DS i) p := by
  by_cases h4 : i < 4
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover0 i h4
    rwa [Nat.zero_add] at h
  by_cases h11 : 11 ≤ i
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover8 (i - 11) (by omega)
    rwa [Nat.add_sub_cancel' h11] at h
  have hc : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover1 0 (by norm_num)
    rwa [Nat.add_zero] at h
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover2 0 (by norm_num)
    rwa [Nat.add_zero] at h
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover3 0 (by norm_num)
    rwa [Nat.add_zero] at h
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover4 0 (by norm_num)
    rwa [Nat.add_zero] at h
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover5 0 (by norm_num)
    rwa [Nat.add_zero] at h
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover6 0 (by norm_num)
    rwa [Nat.add_zero] at h
  · have h := CFSG.Certificates.TwDce3.coverRangeS_sound cover7 0 (by norm_num)
    rwa [Nat.add_zero] at h

theorem cover_pt {i : ℕ} (hi : i < 15) {p : ℕ} (hp : p < 11172) :
    ∃ f < 18934, dKind (RD f) < 3 ∧ dN1 (RD f) = CFSG.KC.LaneChain.getN DS i ∧ dN2 (RD f) ∈ DS ∧
      ∃ g ∈ onSt (CFSG.KC.LaneChain.getN DS i), p = onPtO ((wVal xD (RW f))⁻¹ * g) 0 := by
  obtain ⟨f, hf, hk1, hn1, hn2, cs, hcs, hpe⟩ := reached hi p hp
  have h0 : CFSG.KC.TwDce3.evP 14 FO (wInv INVM (RW f)) 0 = onPtO (wVal xD (RW f))⁻¹ 0 := by
    rw [evP_O (wInv_lt (rw_lt hf)) (by norm_num), wVal_wInv (fun c hc => xD_ivL hc) (rw_lt hf)]
  obtain ⟨g, hg, he⟩ := fold_pt cs hcs (wVal xD (RW f))⁻¹
  rw [h0] at hpe
  exact ⟨f, hf, Nat.blt_eq.mp hk1, hn1, hn2, g, hg, hpe.trans he⟩

@[expose] noncomputable def onS0 : Subgroup onQ where
  carrier := {q | onPtO q 0 = 0}
  mul_mem' {a b} ha hb := by
    have ha' : onPtO a 0 = 0 := ha
    have hb' : onPtO b 0 = 0 := hb
    change onPtO (a * b) 0 = 0
    rw [onPtO_mul, ha', hb']
  one_mem' := onPtO_one 0
  inv_mem' {a} ha := by
    have ha' : onPtO a 0 = 0 := ha
    change onPtO a⁻¹ 0 = 0
    have h := onPtO_mul a a⁻¹ 0
    rw [mul_inv_cancel, onPtO_one, ha'] at h
    exact h.symm

theorem mem_onS0 {q : onQ} : q ∈ onS0 ↔ onPtO q 0 = 0 := Iff.rfl

theorem card_onS0_le : Nat.card onS0 ≤ 168 := by
  let φ : onQ ⧸ onS0 → Fin 11172 := fun z => Quotient.liftOn' z
    (fun a => (⟨onPtO a⁻¹ 0, onPtO_lt _ (by norm_num)⟩ : Fin 11172)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply Fin.ext
      change onPtO a⁻¹ 0 = onPtO b⁻¹ 0
      have e : b⁻¹ = (a⁻¹ * b)⁻¹ * a⁻¹ := by group
      rw [e, onPtO_mul, mem_onS0.1 (onS0.inv_mem hab)])
  have hsurj : Function.Surjective φ := by
    intro p
    obtain ⟨f, -, -, -, -, g, -, he⟩ := cover_pt (i := 0) (by norm_num) p.2
    refine ⟨((((wVal xD (RW f))⁻¹ * g)⁻¹ : onQ) : onQ ⧸ onS0), Fin.ext ?_⟩
    change onPtO ((wVal xD (RW f))⁻¹ * g)⁻¹⁻¹ 0 = p
    rw [inv_inv, ← he]
  have h1 : 11172 ≤ onS0.index := by
    rw [Subgroup.index_eq_card]
    have := Nat.card_le_card_of_surjective φ hsurj
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h2 := onS0.card_mul_index
  have hQ : Nat.card onQ ≤ 1876896 := card_mainWs₁_le.2
  by_contra h
  have h3 := Nat.mul_le_mul (Nat.succ_le_of_lt (not_le.1 h)) h1
  omega

theorem onK1_le : onK 1 ≤ onS0 := by
  rw [onK, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  change onPtO _ 0 = 0
  have hb := CFSG.Certificates.TwDce2.Words.wBelow_spec (gens_all 1 (by norm_num) c hc)
  rw [← evP_O (fun d hd => hb.2 d hd) (by norm_num)]
  exact node1_fix c hc

theorem onS0_eq : onK 1 = onS0 := by
  have h := card_onK_ge (i := 1) (by norm_num)
  rw [cn_one] at h
  exact Subgroup.eq_of_le_of_card_ge onK1_le (card_onS0_le.trans h)

theorem pi_S0_le {q : onQ} (hq : q ∈ onS0) : onPi q ∈ onC := by
  rw [← onS0_eq] at hq
  have : (onK 1).map onPi ≤ onC := by
    rw [onK, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, ← wVal_onPi, wVal, evalWord]
    refine onC.list_prod_mem fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    exact onX_memC (gens1_ok c hc d hd)
  exact this ⟨q, hq, rfl⟩

theorem relIndex_map_onPi_le (P : Subgroup onQ) : (P.map onPi).relIndex onPi.range ≤ P.index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le le_sup_left)

theorem idx_le (i : Fin 15) : ((onSt (CFSG.KC.LaneChain.getN DS i)).map onPi).relIndex onHP ≤
    1876896 / CFSG.KC.LaneChain.getN CN i := by
  rw [← range_onPi]
  refine (relIndex_map_onPi_le _).trans ?_
  rw [Nat.le_div_iff_mul_le (cn_pos i i.2)]
  have h1 := (card_onK_ge i.2).trans (Subgroup.card_le_of_le (onK_le_onSt i.2))
  calc (onSt (CFSG.KC.LaneChain.getN DS i)).index * CFSG.KC.LaneChain.getN CN i ≤
        (onSt (CFSG.KC.LaneChain.getN DS i)).index *
          Nat.card (onSt (CFSG.KC.LaneChain.getN DS i)) := Nat.mul_le_mul_left _ h1
    _ = Nat.card onQ := (onSt _).index_mul_card
    _ ≤ 1876896 := card_mainWs₁_le.2

theorem index_onHP_le : onHP.FiniteIndex ∧ onHP.index ≤ 736560 := by
  classical
  obtain ⟨X, hX0, hX⟩ := factsP
  let repS : Fin 15 → Set onPC := fun i => {k | ∃ f < 18934, dKind (RD f) < 3 ∧
    dN1 (RD f) = CFSG.KC.LaneChain.getN DS i ∧ dN2 (RD f) ∈ DS ∧ k = wVal onX (RW f)}
  let tP : Fin 15 → onPC → Prop := fun i k =>
    ∃ j : Fin 15, ∃ v, v ∈ onHP ∧ X (CFSG.KC.LaneChain.getN DS i) * k * onT *
      (X (CFSG.KC.LaneChain.getN DS j) * v)⁻¹ ∈ onHP
  have htP : ∀ i : Fin 15, ∀ k ∈ repS i, tP i k := by
    rintro i _ ⟨f, hf, hk, hn1, hn2, rfl⟩
    obtain ⟨j, hj⟩ := ds_mem _ hn2
    have hfa := (hX f hf).2.2.2.1 hk
    refine ⟨j, wVal onX (RA f), wVal_mem _, ?_⟩
    rw [hj, ← hn1]
    exact hfa
  let D : TwistData onHP onC onT 15 :=
    { x := fun i => X (CFSG.KC.LaneChain.getN DS i)
      S := fun i => (onSt (CFSG.KC.LaneChain.getN DS i)).map onPi
      rep := repS
      tgt := fun i k => if h : tP i k then h.choose else 0
      tgtElt := fun i k => if h : tP i k then h.choose_spec.choose else 1
      base := 0
      base_mem := by
        change X (CFSG.KC.LaneChain.getN DS 0) ∈ onHP
        rw [ds_zero, hX0]
        exact onHP.one_mem
      S_le := fun i => by
        rw [← range_onPi]
        exact Subgroup.map_le_range _ _
      S_conj := by
        rintro i _ ⟨q, hq, rfl⟩
        induction hq using Subgroup.closure_induction with
        | mem q hq =>
          obtain ⟨c, hc, rfl⟩ := hq
          obtain ⟨hg, hk3, -, hn1, hn2⟩ := isStabOf_sound hc
          have hf := (hX (c / 2) hg).2.2.2.2 hk3
          rw [hn1, hn2] at hf
          rw [← wVal_onPi, wVal_gWord hinvX hg]
          split_ifs
          · convert hf using 1
            group
          · convert onHP.inv_mem hf using 1
            group
        | one => rw [map_one, mul_one, mul_inv_cancel]; exact onHP.one_mem
        | mul a b _ _ ha hb =>
          have e : X (CFSG.KC.LaneChain.getN DS i) * onPi (a * b) *
              (X (CFSG.KC.LaneChain.getN DS i))⁻¹ =
              (X (CFSG.KC.LaneChain.getN DS i) * onPi a * (X (CFSG.KC.LaneChain.getN DS i))⁻¹) *
                (X (CFSG.KC.LaneChain.getN DS i) * onPi b *
                  (X (CFSG.KC.LaneChain.getN DS i))⁻¹) := by
            rw [map_mul]; group
          rw [e]
          exact onHP.mul_mem ha hb
        | inv a _ ha =>
          have e : X (CFSG.KC.LaneChain.getN DS i) * onPi a⁻¹ *
              (X (CFSG.KC.LaneChain.getN DS i))⁻¹ =
              (X (CFSG.KC.LaneChain.getN DS i) * onPi a *
                (X (CFSG.KC.LaneChain.getN DS i))⁻¹)⁻¹ := by
            rw [map_inv]; group
          rw [e]
          exact onHP.inv_mem ha
      rep_le := by
        rintro i _ ⟨f, -, -, -, -, rfl⟩
        exact wVal_mem _
      rep_cover := by
        intro i h hh
        rw [← range_onPi] at hh
        obtain ⟨q, rfl⟩ := hh
        obtain ⟨f, hf, hk, hn1, hn2, g, hg, hp⟩ :=
          cover_pt i.2 (onPtO_lt q⁻¹ (p := 0) (by norm_num))
        have hc : (wVal xD (RW f))⁻¹ * g * q ∈ onS0 := by
          rw [mem_onS0, onPtO_mul, ← hp, ← onPtO_mul, inv_mul_cancel, onPtO_one]
        refine ⟨wVal onX (RW f), ⟨f, hf, hk, hn1, hn2, rfl⟩, onPi g⁻¹,
          ⟨g⁻¹, (onSt _).inv_mem hg, rfl⟩, onPi ((wVal xD (RW f))⁻¹ * g * q), pi_S0_le hc, ?_⟩
        rw [wVal_onPi, ← map_mul, ← map_mul]
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
  have : Finite onHP := by
    rw [← range_onPi]
    exact Finite.of_surjective _ onPi.rangeRestrict_surjective
  obtain ⟨hfi, hle⟩ := D.index_le_sum_of_finite
    (fun c hc => by rw [onC_conj hc]; exact onC_le hc) hgen
  refine ⟨hfi, hle.trans ?_⟩
  calc ∑ i, (D.S i).relIndex onHP ≤ ∑ i : Fin 15, 1876896 / CFSG.KC.LaneChain.getN CN i :=
        Finset.sum_le_sum fun i _ => idx_le i
    _ = 736560 := cn_sum

end CFSG.KD.ONCoverDce3

end
