module

public import Certificates.Kernel.Fi23Q.SubGlue
public import Certificates.Kernel.Fi23Q.SubClsDefs
import Certificates.Kernel.Fi23Q.SubNpAll
public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Q

attribute [local irreducible] sE

open CFSG.Sporadic.Fi23 CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KS.Pc3 CFSG.KS.Fi23Q
  CFSG.Perm CFSG.Sporadic.Th CFSG.KD.Fi23K CFSG.KS.Raw.Orb
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem vecOK9_lt {u : ℕ} (h : vecOK 9 u = true) : u < 4 ^ 9 := by
  obtain ⟨h1, -⟩ := band_true h
  simp only [Nat.blt_eq] at h1
  simpa [Nat.shiftLeft_eq] using h1

theorem eq_of_dg : ∀ {n u v : ℕ}, u < 4 ^ n → v < 4 ^ n → (∀ k < n, dg u k = dg v k) → u = v
  | 0, u, v, hu, hv, _ => by simp at hu hv; omega
  | n + 1, u, v, hu, hv, h => by
    have h0 := h 0 (by omega)
    rw [dg_eq, dg_eq, pow_zero, Nat.div_one, Nat.div_one] at h0
    have e : u / 4 = v / 4 := eq_of_dg (n := n) (by rw [pow_succ] at hu; omega)
      (by rw [pow_succ] at hv; omega) fun k hk => by
        have := h (k + 1) (by omega)
        rwa [dg_eq, dg_eq, pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
          ← dg_eq, ← dg_eq] at this
    omega

@[expose] def Ok9 (w : ℕ) : Prop := w < 4 ^ 9 ∧ ∀ k < 9, dg w k < 3

theorem ok9_of_vecOK {u : ℕ} (h : vecOK 9 u = true) : Ok9 u :=
  ⟨vecOK9_lt h, fun k _ => vecOK9_dg h k⟩

theorem nvS_inj
    {u v : ℕ} (hu : Ok9 u) (hv : Ok9 v)
    (h : nv sE 9 u = nv sE 9 v) : u = v := by
  let α := {w : ℕ // Ok9 w}
  have : Finite α := Finite.of_injective (fun w : α => (⟨w.1, w.2.1⟩ : Fin (4 ^ 9)))
    fun a b e => Subtype.ext (by simpa using congrArg Fin.val e)
  let f : α → SubS := fun w => ⟨nv sE 9 w.1, nvS_mem _⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨w, hw, rfl⟩ := nfS hy
    exact ⟨⟨w, ok9_of_vecOK hw⟩, rfl⟩
  have hg : Function.Injective
      (fun w : α => fun k : Fin 9 => (⟨dg w.1 k, w.2.2 k k.isLt⟩ : Fin 3)) := by
    intro a b e
    apply Subtype.ext
    refine eq_of_dg a.2.1 b.2.1 fun k hk => ?_
    have := congrFun e ⟨k, hk⟩
    simpa using congrArg Fin.val this
  have hc : Nat.card α ≤ Nat.card SubS := by
    rw [card_S]
    calc Nat.card α ≤ Nat.card (Fin 9 → Fin 3) := Nat.card_le_card_of_injective _ hg
      _ = 3 ^ 9 := by simp [Nat.card_eq_fintype_card]
  have hinj := (hf.bijective_of_nat_card_le hc).1
  have := @hinj ⟨u, hu⟩ ⟨v, hv⟩ (Subtype.ext h)
  exact congrArg Subtype.val this

@[expose] noncomputable def vS (x : CFSG.Sporadic.Fi23.J) : ℕ :=
  open Classical in
  if h : ∃ v, vecOK 9 v = true ∧ nv sE 9 v = x then h.choose else 0

theorem vS_spec
    {x : CFSG.Sporadic.Fi23.J} (hx : x ∈ SubS) :
    vecOK 9 (vS x) = true ∧ nv sE 9 (vS x) = x := by
  have h := nfS hx
  unfold vS
  rw [dif_pos h]
  exact h.choose_spec

@[expose] def Ok5 (w : ℕ) : Prop := w < 4 ^ 5 ∧ ∀ c < 5, dg w c < 3

theorem dg_bits (w c : ℕ) :
    dg w c = (w.testBit (2 * c)).toNat + 2 * (w.testBit (2 * c + 1)).toNat := by
  have e1 : (2 : ℕ) ^ (2 * c) = 4 ^ c := by
    rw [pow_mul]
    norm_num
  have e2 : (2 : ℕ) ^ (2 * c + 1) = 4 ^ c * 2 := by rw [pow_succ, e1]
  rw [dg_eq, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, e1, e2,
    ← Nat.div_div_eq_div_mul]
  generalize w / 4 ^ c = q
  rcases Nat.mod_two_eq_zero_or_one q with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (q / 2) with h2 | h2 <;> simp [h1, h2] <;> omega

theorem t341_0 : Nat.testBit 341 0 = true := by decide
theorem t341_1 : Nat.testBit 341 1 = false := by decide
theorem t341_2 : Nat.testBit 341 2 = true := by decide
theorem t341_3 : Nat.testBit 341 3 = false := by decide
theorem t341_4 : Nat.testBit 341 4 = true := by decide
theorem t341_5 : Nat.testBit 341 5 = false := by decide
theorem t341_6 : Nat.testBit 341 6 = true := by decide
theorem t341_7 : Nat.testBit 341 7 = false := by decide
theorem t341_8 : Nat.testBit 341 8 = true := by decide
theorem t341_9 : Nat.testBit 341 9 = false := by decide

theorem add3_eq (u v : ℕ) : add3 u v =
    (fun al ah bl bh => (fun az bz => ((az &&& bl) ||| ((al &&& bz) ||| (ah &&& bh))) |||
      (((az &&& bh) ||| ((ah &&& bz) ||| (al &&& bl))) <<< 1))
      (341 ^^^ (al ||| ah)) (341 ^^^ (bl ||| bh)))
    (u &&& 341) ((u >>> 1) &&& 341) (v &&& 341) ((v >>> 1) &&& 341) := rfl

theorem neg3_eq (u : ℕ) : neg3 u = ((u &&& 341) <<< 1) ||| ((u >>> 1) &&& 341) := rfl

theorem dg_add3 {u v c : ℕ} (hc : c < 5) (hu : dg u c < 3) (hv : dg v c < 3) :
    dg (add3 u v) c = (dg u c + dg v c) % 3 := by
  rw [dg_bits] at hu hv ⊢
  rw [dg_bits u, dg_bits v, add3_eq]
  generalize hA0 : u.testBit (2 * c) = A0 at hu ⊢
  generalize hA1 : u.testBit (2 * c + 1) = A1 at hu ⊢
  generalize hB0 : v.testBit (2 * c) = B0 at hv ⊢
  generalize hB1 : v.testBit (2 * c + 1) = B1 at hv ⊢
  interval_cases c <;>
  · simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hA0 hA1 hB0 hB1 ⊢
    simp only [hA0, hA1, hB0, hB1, t341_0, t341_1, t341_2, t341_3, t341_4, t341_5, t341_6,
      t341_7, t341_8, t341_9, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and]
    revert hu hv
    cases A0 <;> cases A1 <;> cases B0 <;> cases B1 <;> decide

theorem dg_neg3 {u c : ℕ} (hc : c < 5) (hu : dg u c < 3) : dg (neg3 u) c = (2 * dg u c) % 3 := by
  rw [dg_bits] at hu ⊢
  rw [dg_bits u, neg3_eq]
  generalize hA0 : u.testBit (2 * c) = A0 at hu ⊢
  generalize hA1 : u.testBit (2 * c + 1) = A1 at hu ⊢
  interval_cases c <;>
  · simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hA0 hA1 ⊢
    simp only [hA0, hA1, t341_0, t341_1, t341_2, t341_3, t341_4, t341_5, t341_6,
      t341_7, t341_8, t341_9, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and]
    revert hu
    cases A0 <;> cases A1 <;> decide

theorem add3_lt (u v : ℕ) : add3 u v < 4 ^ 5 := by
  rw [add3_eq]
  have m : ∀ x : ℕ, x &&& 341 < 2 ^ 9 := fun x => Nat.and_lt_two_pow x (by norm_num)
  have l : ∀ x y : ℕ, y < 2 ^ 9 → x &&& y < 2 ^ 10 := fun x y hy =>
    lt_of_lt_of_le (Nat.and_lt_two_pow x hy) (by norm_num)
  have r : ∀ x y : ℕ, x < 2 ^ 9 → x &&& y < 2 ^ 9 := fun x y hx =>
    lt_of_le_of_lt Nat.and_le_left hx
  have e : (4 : ℕ) ^ 5 = 2 ^ 10 := by norm_num
  rw [e]
  dsimp only
  refine Nat.or_lt_two_pow (Nat.or_lt_two_pow (l _ _ (m v)) (Nat.or_lt_two_pow
    (lt_of_lt_of_le (r _ _ (m u)) (by norm_num)) (l _ _ (m (v >>> 1))))) ?_
  rw [Nat.shiftLeft_eq, pow_one]
  have : ((341 ^^^ ((u &&& 341) ||| ((u >>> 1) &&& 341))) &&& ((v >>> 1) &&& 341) |||
      ((((u >>> 1) &&& 341) &&& (341 ^^^ ((v &&& 341) ||| ((v >>> 1) &&& 341)))) |||
        ((u &&& 341) &&& (v &&& 341)))) < 2 ^ 9 :=
    Nat.or_lt_two_pow (Nat.and_lt_two_pow _ (m _))
      (Nat.or_lt_two_pow (r _ _ (m _)) (Nat.and_lt_two_pow _ (m _)))
  omega

theorem ok5_add3 {u v : ℕ} (hu : Ok5 u) (hv : Ok5 v) : Ok5 (add3 u v) :=
  ⟨add3_lt u v, fun c hc => by rw [dg_add3 hc (hu.2 c hc) (hv.2 c hc)]; omega⟩

theorem neg3_lt (u : ℕ) : neg3 u < 4 ^ 5 := by
  rw [neg3_eq, Nat.shiftLeft_eq, pow_one]
  have h1 : u &&& 341 < 2 ^ 9 := Nat.and_lt_two_pow (n := 9) u (by norm_num)
  have h2 : (u >>> 1) &&& 341 < 2 ^ 9 := Nat.and_lt_two_pow (n := 9) _ (by norm_num)
  have h1' : (u &&& 341) * 2 < 2 ^ 10 := by omega
  have h2' : (u >>> 1) &&& 341 < 2 ^ 10 := by omega
  have e : (4 : ℕ) ^ 5 = 2 ^ 10 := by norm_num
  rw [e]
  exact Nat.or_lt_two_pow h1' h2'

theorem ok5_neg3 {u : ℕ} (hu : Ok5 u) : Ok5 (neg3 u) :=
  ⟨neg3_lt u, fun c hc => by rw [dg_neg3 hc (hu.2 c hc)]; omega⟩

theorem ok5_sub3 {u v : ℕ} (hu : Ok5 u) (hv : Ok5 v) : Ok5 (sub3 u v) := ok5_add3 hu (ok5_neg3 hv)

theorem ok5_smul3 {e u : ℕ} (hu : Ok5 u) : Ok5 (smul3 e u) := by
  unfold smul3
  simp only [CFSG.KS.PK.nIf_eq]
  split_ifs
  · exact ⟨by norm_num, fun c _ => by rw [dg_eq]; simp⟩
  · exact hu
  · exact ok5_neg3 hu

theorem cr_conj_of
    (aE : ℕ → CFSG.Sporadic.Fi23.J)
    (hH : ∀ k < 13, ∀ x < 31671, tb CFSG.KD.Fi23Q.H k x = idx 31671 (aE k) x) {q c n W : ℕ}
    (h : CFSG.KD.Fi23Q.wordK q c n W = true) (hc : c < 4) :
    IsConj (((nwR 13 (f32 CFSG.KD.Fi23Q.CR q)).map aE).prod) (t3 ⟨c, hc⟩) := by
  unfold CFSG.KD.Fi23Q.wordK at h
  obtain ⟨-, -, hw, hb⟩ := clsW_spec h
  have hwok : ∀ r ∈ cwR n W, RegOK r := fun r hr => by
    obtain ⟨l, hl, rfl⟩ := hw r hr
    right
    omega
  set E := ((nwR 13 (f32 CFSG.KD.Fi23Q.CR q)).map aE).prod with hE
  set Wd := ((cwR n W).map regE).prod with hWd
  have key : Wd * E = t3 ⟨c, hc⟩ * Wd := eq_of_base fun t ht => by
    have ht' : t < 31671 := by omega
    have e := hb t ht
    have k1 : wv CFSG.KD.Fi23Q.H (nwR 13 (f32 CFSG.KD.Fi23Q.CR q)) t = idx 31671 E t :=
      wv_eq_of (P := fun r => r < 13) (fun r hr => hH r hr) _ (fun r hr => nwR_lt hr) t ht'
    have k2 : wv CFSG.KD.Fi23K.G (cwR n W) (idx 31671 E t) = idx 31671 Wd (idx 31671 E t) :=
      wvG_eq _ hwok _ (idx_lt E ht')
    have k3 : wv CFSG.KD.Fi23K.G (cwR n W) t = idx 31671 Wd t := wvG_eq _ hwok t ht'
    have k4 : wv CFSG.KD.Fi23K.G (CFSG.KD.Fi23Q.t3R c) (idx 31671 Wd t) =
        idx 31671 (t3 ⟨c, hc⟩) (idx 31671 Wd t) := by
      rw [wvG_eq _ (t3R_ok hc) _ (idx_lt Wd ht'), t3R_prod hc]
    rw [k1, k2, k3, k4] at e
    rw [idx_mul, idx_mul]
    exact e
  exact isConj_iff.2 ⟨Wd, by rw [key, mul_inv_cancel_right]⟩

theorem npK_conj
    {v b q c n W : ℕ} (h : CFSG.KD.Fi23Q.npK v b q c n W = true) :
    vecOK 9 v = true ∧ (IsConj (nv sE 9 v) (t3 0) ∨ IsConj (nv sE 9 v) (t3 2)) := by
  unfold CFSG.KD.Fi23Q.npK conjW at h
  obtain ⟨hc, h⟩ := band_true h
  obtain ⟨hw, h⟩ := band_true h
  obtain ⟨hv, h⟩ := band_true h
  obtain ⟨hb, he⟩ := band_true h
  have he : eqH CFSG.KD.Fi23Q.H (swR 9 CFSG.KD.Fi23Q.SubV v ++ nwR 13 b)
      (nwR 13 b ++ nwR 13 (f32 CFSG.KD.Fi23Q.CR q)) = true := he
  have hE := eqH_rep aE aE_acts
  obtain ⟨W1, W2⟩ := swS_spec hv
  obtain ⟨B1, B2⟩ := nwR_spec aE (vecOK_dg hb)
  have e := eqH_wd hE (allLt_append W2 B2) (allLt_append B2 fun r hr => nwR_lt hr) he
  rw [wd_append, wd_append, W1] at e
  have hc4 : c < 4 := (clsW_spec (by unfold CFSG.KD.Fi23Q.wordK at hw; exact hw)).2.1
  have hx : IsConj (nv sE 9 v) (((nwR 13 (f32 CFSG.KD.Fi23Q.CR q)).map aE).prod) := by
    refine isConj_iff.2 ⟨(wd aE (nwR 13 b))⁻¹, ?_⟩
    rw [inv_inv, mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
    rfl
  have hk := hx.trans (cr_conj_of aE aE_acts hw hc4)
  refine ⟨hv, ?_⟩
  interval_cases c
  · exact Or.inl hk
  · exact absurd hc (by decide)
  · exact Or.inr hk
  · exact absurd hc (by decide)

theorem npV_ne : ∀ k < 131, CFSG.KD.Fi23Q.npV.getD k 0 ≠ 0 := by decide +kernel

theorem np_conj
    {k : ℕ} (hk : k < 131) :
    vecOK 9 (CFSG.KD.Fi23Q.npV.getD k 0) = true ∧ nv sE 9 (CFSG.KD.Fi23Q.npV.getD k 0) ≠ 1 ∧
      (IsConj (nv sE 9 (CFSG.KD.Fi23Q.npV.getD k 0)) (t3 0) ∨
        IsConj (nv sE 9 (CFSG.KD.Fi23Q.npV.getD k 0)) (t3 2)) := by
  obtain ⟨hv, hc⟩ := npK_conj (CFSG.KD.Fi23Q.npAll k hk)
  refine ⟨hv, fun h1 => npV_ne k hk ?_, hc⟩
  rw [← nv_zero9 sE] at h1
  exact nvS_inj (ok9_of_vecOK hv) (ok9_of_vecOK (by decide)) h1

section Gen

variable {G : Type*} [Group G]

@[expose] noncomputable def epsG (x : ℕ → G) (w : ℕ) : G :=
  ((List.range 5).map fun c => x (4 + c) ^ dg w c).prod

@[expose] noncomputable def tauG (x : ℕ → G) (a : ℕ) : G :=
  ((List.range 4).map fun k => x k ^ dg a k).prod

theorem epsG_zero (x : ℕ → G) : epsG x 0 = 1 := by
  unfold epsG
  apply List.prod_eq_one
  intro g hg
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hg
  rw [dg_eq, Nat.zero_div, Nat.zero_mod, pow_zero]

theorem tauG_zero (x : ℕ → G) : tauG x 0 = 1 := by
  unfold tauG
  apply List.prod_eq_one
  intro g hg
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hg
  rw [dg_eq, Nat.zero_div, Nat.zero_mod, pow_zero]

theorem epsG_congr (x : ℕ → G) {u v : ℕ} (h : ∀ c < 5, dg u c = dg v c) : epsG x u = epsG x v := by
  unfold epsG
  apply congrArg
  apply List.map_congr_left
  intro c hc
  rw [h c (List.mem_range.1 hc)]

theorem epsG_unit (x : ℕ → G) {c : ℕ} (hc : c < 5) : epsG x (4 ^ c) = x (4 + c) := by
  unfold epsG
  rw [prod_range_single _ 5 hc fun m _ hmc => by rw [dg_unit, if_neg hmc, pow_zero]]
  rw [dg_unit, if_pos rfl, pow_one]

end Gen

noncomputable abbrev eps (w : ℕ) : CFSG.Sporadic.Fi23.J := epsG sE w

noncomputable abbrev tau (a : ℕ) : CFSG.Sporadic.Fi23.J := tauG sE a

@[expose] def Ok4 (a : ℕ) : Prop := a < 4 ^ 4 ∧ ∀ k < 4, dg a k < 3

theorem dg_lowV4 (v : ℕ) {k : ℕ} (hk : k < 4) : dg (lowV v 4) k = dg v k := by
  rw [lowV_eq, dg_eq, dg_eq]
  have e : (4 : ℕ) ^ 4 = 4 ^ k * 4 ^ (4 - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 4 (by omega))]

theorem shr8_eq (v : ℕ) : Nat.shiftRight v 8 = v / 256 := Nat.shiftRight_eq_div_pow v 8

theorem dg_shr8 (v c : ℕ) : dg (Nat.shiftRight v 8) c = dg v (4 + c) := by
  rw [dg_eq, dg_eq, shr8_eq, Nat.div_div_eq_div_mul, pow_add]
  norm_num

theorem nvG_split {G : Type*} [Group G] (x : ℕ → G) (v : ℕ) :
    nv x 9 v = tauG x (lowV v 4) * epsG x (Nat.shiftRight v 8) := by
  unfold nv tauG epsG
  have e9 : List.range 9 = List.range 4 ++ (List.range 5).map (4 + ·) := @List.range_add 4 5
  rw [e9, List.map_append, List.prod_append, List.map_map]
  refine congrArg₂ (· * ·) (congrArg List.prod (List.map_congr_left fun k hk => ?_))
    (congrArg List.prod (List.map_congr_left fun c _ => ?_))
  · rw [dg_lowV4 v (List.mem_range.1 hk)]
  · simp only [Function.comp_apply, dg_shr8]

theorem nv_split (v : ℕ) :
    nv sE 9 v = tau (lowV v 4) * eps (Nat.shiftRight v 8) := nvG_split sE v

theorem lowV_te (a w : ℕ) (ha : a < 4 ^ 4) : lowV (a + 256 * w) 4 = a := by
  rw [lowV_eq]
  norm_num at ha ⊢
  omega

theorem shr8_te (a w : ℕ) (ha : a < 4 ^ 4) : Nat.shiftRight (a + 256 * w) 8 = w := by
  rw [shr8_eq]
  norm_num at ha
  omega

theorem te_nv {a w : ℕ} (ha : a < 4 ^ 4) :
    tau a * eps w = nv sE 9 (a + 256 * w) := by
  rw [nv_split, lowV_te a w ha, shr8_te a w ha]

theorem ok9_te {a w : ℕ} (ha : Ok4 a) (hw : Ok5 w) : Ok9 (a + 256 * w) := by
  refine ⟨by have := ha.1; have := hw.1; norm_num at *; omega, fun k hk => ?_⟩
  by_cases h4 : k < 4
  · rw [← dg_lowV4 _ h4, lowV_te a w ha.1]
    exact ha.2 k h4
  · obtain ⟨c, rfl⟩ : ∃ c, k = 4 + c := ⟨k - 4, by omega⟩
    rw [← dg_shr8, shr8_te a w ha.1]
    exact hw.2 c (by omega)

theorem te_inj
    {a a' w w' : ℕ} (ha : Ok4 a) (ha' : Ok4 a') (hw : Ok5 w)
    (hw' : Ok5 w') (h : tau a * eps w = tau a' * eps w') : a = a' ∧ w = w' := by
  rw [te_nv ha.1, te_nv ha'.1] at h
  have e := nvS_inj (ok9_te ha hw) (ok9_te ha' hw') h
  have := ha.1
  have := ha'.1
  norm_num at *
  omega

theorem te_of_mem
    {x : CFSG.Sporadic.Fi23.J} (hx : x ∈ SubS) :
    ∃ a w, Ok4 a ∧ Ok5 w ∧ x = tau a * eps w := by
  obtain ⟨hv, e⟩ := vS_spec hx
  have h9 := ok9_of_vecOK hv
  refine ⟨lowV (vS x) 4, Nat.shiftRight (vS x) 8, ⟨?_, fun k hk => ?_⟩, ⟨?_, fun c hc => ?_⟩, ?_⟩
  · rw [lowV_eq]
    exact Nat.mod_lt _ (by norm_num)
  · rw [dg_lowV4 _ hk]
    exact h9.2 k (by omega)
  · rw [shr8_eq]
    have := h9.1
    norm_num at *
    omega
  · rw [dg_shr8]
    exact h9.2 _ (by omega)
  · rw [← nv_split, e]

theorem f32_zero (k : ℕ) : f32 0 k = 0 := by
  unfold f32
  change (0 >>> _) &&& _ = 0
  simp

section Prods

variable {G : Type*} [Group G]

theorem prod_pow_mul (g : ℕ → G) {N : ℕ} (hc : ∀ i < N, ∀ j < N, Commute (g i) (g j))
    (h3 : ∀ i < N, g i ^ 3 = 1) (a b : ℕ → ℕ) : ∀ n ≤ N,
    ((List.range n).map fun c => g c ^ a c).prod * ((List.range n).map fun c => g c ^ b c).prod =
      ((List.range n).map fun c => g c ^ ((a c + b c) % 3)).prod
  | 0, _ => by simp
  | n + 1, hn => by
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    have ih := prod_pow_mul g hc h3 a b n (by omega)
    have hcomm : Commute (g n ^ a n) ((List.range n).map fun c => g c ^ b c).prod := by
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hy
      exact (hc n (by omega) c (by have := List.mem_range.1 hc'; omega)).pow_pow _ _
    rw [mul_assoc, ← mul_assoc (g n ^ a n), hcomm.eq, mul_assoc, ← pow_add, ← mul_assoc, ih,
      ← pow_eq_pow_mod _ (h3 n (by omega))]

theorem epsG_add (x : ℕ → G) (hc : ∀ i < 5, ∀ j < 5, Commute (x (4 + i)) (x (4 + j)))
    (h3 : ∀ i < 5, x (4 + i) ^ 3 = 1) {u v : ℕ} (hu : ∀ c < 5, dg u c < 3)
    (hv : ∀ c < 5, dg v c < 3) : epsG x (add3 u v) = epsG x u * epsG x v := by
  have key := prod_pow_mul (N := 5) (fun c => x (4 + c)) hc h3 (dg u) (dg v) 5 le_rfl
  unfold epsG
  rw [key]
  apply congrArg
  apply List.map_congr_left
  intro c hc
  rw [dg_add3 (List.mem_range.1 hc) (hu c (List.mem_range.1 hc)) (hv c (List.mem_range.1 hc))]

end Prods

theorem eps_zero : eps 0 = 1 := epsG_zero sE

theorem eps_congr {u v : ℕ} (h : ∀ c < 5, dg u c = dg v c) :
    eps u = eps v := epsG_congr sE h

theorem eps_inj
    {u v : ℕ} (hu : Ok5 u) (hv : Ok5 v) (h : eps u = eps v) :
    u = v := by
  have h0 : Ok4 0 := ⟨by norm_num, fun k _ => by rw [dg_eq]; simp⟩
  have e : tau 0 * eps u = tau 0 * eps v := by rw [h]
  exact (te_inj h0 h0 hu hv e).2

theorem tau_zero : tau 0 = 1 := tauG_zero sE

theorem ok5_zero : Ok5 0 := ⟨by norm_num, fun c _ => by rw [dg_eq]; simp⟩

theorem ok5_unit {c : ℕ} (hc : c < 5) : Ok5 (4 ^ c) :=
  ⟨Nat.pow_lt_pow_right (by norm_num) hc, fun d _ => by rw [dg_unit]; split_ifs <;> omega⟩

section Conj

variable {G : Type*} [Group G]

theorem conj_prod (g : G) (l : List G) : g⁻¹ * l.prod * g = (l.map fun x => g⁻¹ * x * g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [← ih]
    group

theorem conj_pow' (g x : G) (n : ℕ) : g⁻¹ * x ^ n * g = (g⁻¹ * x * g) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    group

end Conj

theorem cj_vec {i j : ℕ} (hij : i < j) (hj : j < 9) :
    vecOK 9 (f32 CFSG.KD.Fi23Q.SubCJ (16 * i + j)) = true := by
  have hd := relS_parts.1
  unfold pcDataOK at hd
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff,
    CFSG.KS.PK.strictB_eq] at hd
  have hcj := (hd.2 i (by omega)).2.2 j hj
  simp only [CFSG.KS.PK.bIf_eq, Nat.blt_eq, hij, ↓reduceIte, CFSG.KS.PK.strictB_eq,
    CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, cj_index] at hcj
  exact hcj.1

theorem colE_eq (CJ k c : ℕ) : colE CJ k c = Nat.shiftRight (f32 CJ (16 * k + (4 + c))) 8 := by
  unfold colE
  rw [cj_index]
  try rfl

theorem tauG_eq {G : Type*} [Group G] (x : ℕ → G) (a : ℕ) :
    tauG x a = x 0 ^ dg a 0 * (x 1 ^ dg a 1 * (x 2 ^ dg a 2 * x 3 ^ dg a 3)) := by
  unfold tauG
  simp [List.range_succ, mul_assoc]

theorem tau_eq (a : ℕ) :
    tau a = sE 0 ^ dg a 0 * (sE 1 ^ dg a 1 * (sE 2 ^ dg a 2 * sE 3 ^ dg a 3)) := tauG_eq sE a

end CertificateChecks.KernelFi23Q

end
