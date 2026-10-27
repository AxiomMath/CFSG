module

public import Certificates.Kernel.Sporadic.Fi24Pump.Checks
public import Certificates.Kernel.Sporadic.Fi24Base.Glue
public import Certificates.Kernel.Sporadic.Fi24F3d.Final
public import Certificates.Kernel.Sporadic.Fi24F3d.KneserAut
public import CFSG.Certificates.Kernel.Spor.Fi24PumpKSound
public import CFSG.Sporadic.Fi24.PtGraphBridge
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24PumpFacts

public section

namespace CFSG.KD.Fi24Pump

open CFSG.KC CFSG.KC.Fi24NetPt CFSG.KC.Fi24FixP CFSG.KC.Fi24PumpK CFSG.KC.Fi24Kn CFSG.KS.Fi24Net
  CFSG.KS.Fi24NetPt CFSG.KS.Fi24PumpK CFSG.KD.Fi24Net CFSG.Sporadic.Th CFSG.Perm
  CFSG.Sporadic.Fi24.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
  CertificateChecks.KernelFi24F3d Finset

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Words


theorem wordElt_nil : wordElt [] = 1 := rfl

theorem wordElt_cons (l : ℕ) (w : List ℕ) :
    wordElt (l :: w) = pairG CFSG.Sporadic.Fi24.gs l * wordElt w := by
  unfold wordElt
  rw [List.map_cons, List.prod_cons]

theorem wordElt_append (u v : List ℕ) : wordElt (u ++ v) = wordElt u * wordElt v := by
  unfold wordElt
  rw [List.map_append, List.prod_append]

theorem wordElt_repW (v : List ℕ) : ∀ p, wordElt (repW v p) = wordElt v ^ p
  | 0 => rfl
  | p + 1 => by rw [repW_succ, wordElt_append, wordElt_repW v p, pow_succ']

theorem eq_of_base {x y : CFSG.Sporadic.Fi24.J}
    (h : ∀ b ∈ chainBase.toList, idx 306936 x b = idx 306936 y b) : x = y := by
  have hm : ∀ t < chainBase.size, chainBase[t]! ∈ chainBase.toList := by
    rw [CFSG.Sporadic.Fi24.chainBase_size]
    decide
  have h1 : y⁻¹ * x = 1 := CFSG.Sporadic.Fi24.sep _ fun t ht => by
    rw [idx_mul, h _ (hm t ht), ← idx_mul, inv_mul_cancel, idx_one]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem chainBase_lt' : ∀ b ∈ chainBase.toList, b < 306936 := by decide

theorem card_subtype_fin_eq (n : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    Nat.card {k : Fin n // q k.val} = ((range n).filter q).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hi, hq⟩
    exact ⟨⟨i, hi⟩, hq, rfl⟩

theorem card_fix_eq {g : CFSG.Sporadic.Fi24.J} {F : ℕ → ℕ} (h : ∀ p < 306936, idx 306936 g p = F p) :
    Nat.card {k : Fin 306936 // g • k = k} = #((range 306936).filter fun x => F x = x) := by
  rw [← card_subtype_fin_eq]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
  rw [← h k k.2, idx_of_lt g k.2]
  exact ⟨fun hk => by rw [hk], fun hk => Fin.ext hk⟩

variable (hL : ∀ l < 26, ∀ p < 306936,
  idx 306936 (pairG CFSG.Sporadic.Fi24.gs l) p = LN CFSG.KD.Fi24Net.NW l p)
include hL

theorem idx_wordElt : ∀ w : List ℕ, (∀ l ∈ w, l < 26) → ∀ p < 306936,
    idx 306936 (wordElt w) p = w.foldr (LN CFSG.KD.Fi24Net.NW) p
  | [], _, p, _ => by rw [wordElt_nil, idx_one]; rfl
  | l :: w, hw, p, hp => by
    rw [wordElt_cons, idx_mul, idx_wordElt w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) p hp,
      hL l (hw l List.mem_cons_self) _ ?_, List.foldr_cons]
    rw [← idx_wordElt w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) p hp]
    exact idx_lt _ hp

theorem eq_of_foldr {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26)
    (h : ∀ b ∈ chainBase.toList, u.foldr (LN NW) b = v.foldr (LN NW) b) : wordElt u = wordElt v :=
  eq_of_base fun b hb => by
    rw [idx_wordElt hL u hu b (chainBase_lt' b hb), idx_wordElt hL v hv b (chainBase_lt' b hb), h b hb]

theorem threePair_of {r v : List ℕ} {p n : ℕ} (hp : p.Prime)
    (h : pairOK (CFSG.KC.Fi24Base.eqB (letN NW)) (planeL NW) r v p n = true) :
    ThreePair (wordElt r) p n := by
  have e : letN NW = LN NW := funext fun l => funext fun x => letN_eq NW l x
  rw [e] at h
  obtain ⟨hr, hv, hpow, ⟨b, hb, hne⟩, hcomm, hfix⟩ :=
    pairOK_spec (fun _ hl _ hq => CFSG.KD.Fi24Base.LN_lt19 hl hq)
      (fun _ hl v q _ => testBit_planeL (CFSG.KD.Fi24Base.nv_LN hl) v q) h
  have hvp : ∀ l ∈ repW v p, l < 26 := fun l hl => hv l (mem_repW p hl)
  have hrv : ∀ l ∈ r ++ v, l < 26 := fun l hl => by
    rcases List.mem_append.1 hl with h | h
    · exact hr l h
    · exact hv l h
  have hvr : ∀ l ∈ v ++ r, l < 26 := fun l hl => by
    rcases List.mem_append.1 hl with h | h
    · exact hv l h
    · exact hr l h
  have hP : wordElt v ^ p = 1 := by
    rw [← wordElt_repW, ← wordElt_nil]
    exact eq_of_foldr hL hvp (fun _ h => absurd h List.not_mem_nil) hpow
  have h1 : wordElt v ≠ 1 := by
    intro h1
    apply hne
    rw [← idx_wordElt hL v hv b (chainBase_lt' b hb), h1, idx_one]
  refine ⟨wordElt v, ?_, ?_, ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hP h1
  · rw [← wordElt_append, ← wordElt_append]
    exact eq_of_foldr hL hrv hvr hcomm
  · rw [card_fix_eq (idx_wordElt hL v hv), hfix]

theorem threePairs : ThreePair (fi24Rep3 0) 13 6 ∧ ThreePair (fi24Rep3 1) 11 3 ∧
    ThreePair (fi24Rep3 2) 7 0 ∧ ThreePair (fi24Rep3 4) 13 6 :=
  ⟨threePair_of hL (by norm_num) Ck.p0, threePair_of hL (by norm_num) Ck.p1,
    threePair_of hL (by norm_num) Ck.p2, threePair_of hL (by norm_num) Ck.p3⟩

theorem card_fix_rep3 : Nat.card {k : Fin 306936 // fi24Rep3 3 • k = k} = 162 := by
  have h := CFSG.KD.Fi24Base.fix_ok
  rw [List.all_eq_true] at h
  have h16 := h ([16], 162) (by
    unfold Timmesfeld.Fi24Cl.repFixData
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hw : ∀ l ∈ [16], l < 26 := by decide
  change Nat.card {k : Fin 306936 // wordElt [16] • k = k} = 162
  rw [card_fix_eq (idx_wordElt hL [16] hw)]
  exact CFSG.KS.Fi24FixP.fixOK_spec (σ := LN NW) (fun l hl q hq => CFSG.KD.Fi24Base.LN_lt19 (hw l hl) hq)
    (fun l hl v q _ => testBit_planeL (CFSG.KD.Fi24Base.nv_LN (hw l hl)) v q) h16

end Words

section Five


open CFSG.Sporadic.Fi24 (J cls jR seedGrp ptFix PtAdj pt)

noncomputable def fixPt (g : J) : {k : Fin 306936 // g • k = k} ≃ ptFix (g : GL (Fin 781) (ZMod 3)) :=
  Equiv.ofBijective (fun k => ⟨(pt k.1.val).sp, (CFSG.Sporadic.Fi24.mem_ptFix_iff g k.1).2 k.2⟩)
    ⟨fun k l h => Subtype.ext (CFSG.Sporadic.Fi24.pt_sp_inj (congrArg Subtype.val h)), fun V => by
      obtain ⟨k, hk⟩ := CFSG.Sporadic.Fi24.exists_pt_of_mem_ptFix V.2
      refine ⟨⟨k, (CFSG.Sporadic.Fi24.mem_ptFix_iff g k).1 (by rw [hk]; exact V.2)⟩, ?_⟩
      exact Subtype.ext hk⟩

theorem knJ {g : J} (M : KnModel (g : GL (Fin 781) (ZMod 3)) 9) :
    ∃ φ : {k : Fin 306936 // g • k = k} ≃ KP 9, ∀ k l : {k : Fin 306936 // g • k = k},
      (k.1 ≠ l.1 ∧ cls k.1 * cls l.1 = cls l.1 * cls k.1) ↔ KP.Disj (φ k) (φ l) := by
  obtain ⟨φ, hφ⟩ := M
  refine ⟨(fixPt g).trans φ, fun k l => ?_⟩
  rw [Equiv.trans_apply, Equiv.trans_apply, ← hφ, ← CFSG.Sporadic.Fi24.ptAdj_pt_iff]
  rfl

theorem KP9_deg : ∀ p : KP 9, (univ.filter fun q => KP.Disj q p).card = 21 := by decide

theorem conj_comm_iff {G : Type*} [Group G] (c a b : G) :
    (c * a * c⁻¹) * (c * b * c⁻¹) = (c * b * c⁻¹) * (c * a * c⁻¹) ↔ a * b = b * a := by
  constructor
  · intro hh
    have h1 : c * (a * b) * c⁻¹ = c * (b * a) * c⁻¹ := by
      calc c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
        _ = (c * b * c⁻¹) * (c * a * c⁻¹) := hh
        _ = c * (b * a) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  · intro hh
    calc (c * a * c⁻¹) * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
      _ = c * (b * a) * c⁻¹ := by rw [hh]
      _ = (c * b * c⁻¹) * (c * a * c⁻¹) := by group

noncomputable def actFix {g t : J} (h : t * g = g * t) :
    {k : Fin 306936 // g • k = k} ≃ {k : Fin 306936 // g • k = k} where
  toFun k := ⟨t • k.1, by rw [smul_smul, ← h, mul_smul, k.2]⟩
  invFun k := ⟨t⁻¹ • k.1, by
    have h' : t⁻¹ * g = g * t⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]
    rw [smul_smul, ← h', mul_smul, k.2]⟩
  left_inv k := Subtype.ext (inv_smul_smul t k.1)
  right_inv k := Subtype.ext (smul_inv_smul t k.1)

theorem fiveFix_of_kn {g : J} (M : KnModel (g : GL (Fin 781) (ZMod 3)) 9) : FiveFix g := by
  classical
  obtain ⟨φ, hφ⟩ := knJ M
  refine ⟨?_, fun d hd => ?_, fun t ht h3 => ?_⟩
  · rw [Nat.card_congr φ, Nat.card_eq_fintype_card, card_KP9]
  · set d' : {k : Fin 306936 // g • k = k} := ⟨d, hd⟩
    have e : {k : Fin 306936 // g • k = k ∧ k ≠ d ∧ cls k * cls d = cls d * cls k} ≃
        {q : KP 9 // KP.Disj q (φ d')} :=
      { toFun := fun k => ⟨φ ⟨k.1, k.2.1⟩, (hφ ⟨k.1, k.2.1⟩ d').1 k.2.2⟩
        invFun := fun q => ⟨(φ.symm q.1).1, (φ.symm q.1).2, by
          have := (hφ (φ.symm q.1) d').2
          rw [Equiv.apply_symm_apply] at this
          exact this q.2⟩
        left_inv := fun k => by
          apply Subtype.ext
          simp
        right_inv := fun q => by
          apply Subtype.ext
          simp }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, KP9_deg]
  · set σ := actFix ht
    let σ' : KP 9 ≃ KP 9 := φ.symm.trans (σ.trans φ)
    have hadj : ∀ k l : {k : Fin 306936 // g • k = k},
        (σ k).1 ≠ (σ l).1 ∧ cls (σ k).1 * cls (σ l).1 = cls (σ l).1 * cls (σ k).1 ↔
          k.1 ≠ l.1 ∧ cls k.1 * cls l.1 = cls l.1 * cls k.1 := by
      intro k l
      change t • k.1 ≠ t • l.1 ∧ cls (t • k.1) * cls (t • l.1) = cls (t • l.1) * cls (t • k.1) ↔ _
      rw [CFSG.Sporadic.Fi24.cls_smul, CFSG.Sporadic.Fi24.cls_smul, conj_comm_iff,
        (MulAction.injective t).ne_iff]
    have hσ' : ∀ p q, KP.Disj (σ' p) (σ' q) ↔ KP.Disj p q := by
      intro p q
      change KP.Disj (φ (σ (φ.symm p))) (φ (σ (φ.symm q))) ↔ _
      rw [← hφ, hadj, hφ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hσ3 : ∀ k, σ (σ (σ k)) = k := fun k => by
      apply Subtype.ext
      change t • t • t • k.1 = k.1
      rw [smul_smul, smul_smul, ← pow_three', h3, one_smul]
    have h3' : ∀ p, σ' (σ' (σ' p)) = p := fun p => by
      change φ (σ (φ.symm (φ (σ (φ.symm (φ (σ (φ.symm p)))))))) = p
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hσ3, Equiv.apply_symm_apply]
    have key := aut_fix_mod5 σ' hσ' h3'
    have e : {k : Fin 306936 // g • k = k ∧ t • k = k} ≃ {p : KP 9 // σ' p = p} :=
      { toFun := fun k => ⟨φ ⟨k.1, k.2.1⟩, by
          change φ (σ (φ.symm (φ ⟨k.1, k.2.1⟩))) = φ ⟨k.1, k.2.1⟩
          rw [Equiv.symm_apply_apply]
          congr 1
          exact Subtype.ext k.2.2⟩
        invFun := fun p => ⟨(φ.symm p.1).1, (φ.symm p.1).2, by
          have hp : φ (σ (φ.symm p.1)) = p.1 := p.2
          have : σ (φ.symm p.1) = φ.symm p.1 := by
            rw [← Equiv.apply_eq_iff_eq φ, hp, Equiv.apply_symm_apply]
          exact congrArg Subtype.val this⟩
        left_inv := fun k => by
          apply Subtype.ext
          simp
        right_inv := fun p => by
          apply Subtype.ext
          simp }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact key

noncomputable def eJ : J := ⟨eE, by rw [← CFSG.Sporadic.Fi24.seedGrp_eq_J]; exact eE_mem⟩

noncomputable def fJ : J := ⟨eF, by rw [← CFSG.Sporadic.Fi24.seedGrp_eq_J]; exact eF_mem⟩

theorem coe_eJ_fJ (a b : ℕ) :
    ((eJ ^ a * fJ ^ b : J) : GL (Fin 781) (ZMod 3)) = eE ^ a * eF ^ b := by
  rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
  rfl

theorem five_facts : ∃ e f : J, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧
    (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 → FiveFix (e ^ a * f ^ b) := by
  have hc : ∀ x y : J, (x : GL (Fin 781) (ZMod 3)) = y → x = y := fun x y h => Subtype.ext h
  refine ⟨eJ, fJ, hc _ _ ?_, fun h => eE_ne (congrArg Subtype.val h), hc _ _ ?_, hc _ _ ?_,
    fun k _ h => eF_ne_pow k (by have := congrArg Subtype.val h; rwa [Subgroup.coe_pow] at this),
    fun a ha b hb hab => fiveFix_of_kn (by rw [coe_eJ_fJ]; exact five_kn a ha b hb hab)⟩
  · rw [Subgroup.coe_pow]
    exact eE_pow5
  · rw [Subgroup.coe_pow]
    exact eF_pow5
  · rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact eEF_comm

theorem fi24PumpFacts_of_letters
    (hL : ∀ l < 26, ∀ p < 306936,
      idx 306936 (pairG CFSG.Sporadic.Fi24.gs l) p = LN CFSG.KD.Fi24Net.NW l p) :
    Fi24PumpFacts :=
  ⟨five_facts, (threePairs hL).1, (threePairs hL).2.1, (threePairs hL).2.2.1, (threePairs hL).2.2.2,
    card_fix_rep3 hL⟩

end Five

end CFSG.KD.Fi24Pump

end
