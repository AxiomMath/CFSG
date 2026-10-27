module

public import Certificates.Kernel.Fi23S.Fact1013
public import Certificates.Kernel.Fi23Y.ChkDefs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Y.KSY

open CFSG.KC.Enum CFSG.KD.Fi23K CFSG.KD.Fi23S CFSG.KS.PC CFSG.KS.Raw.Orb CFSG.KS.PEnum
  CFSG.KS.TBfs CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native
  CertificateChecks.KernelFi23S

noncomputable abbrev TY : Subgroup (Equiv.Perm (Fin 31671)) := grp 31671 42 SL

@[expose] noncomputable def lvP (l : Nat) : Equiv.Perm (Fin 31671) := tv 0 (l / 512) * tv 1 (l % 512)

theorem lvP_eq (l : Nat) : lvP l = tv 0 (l / 512) * tv 1 (l % 512) := rfl

theorem leaf_hi_lt {l : Nat} (hl : l < 262144) : l / 512 < 512 := by omega

theorem leaf_lo_lt (l : Nat) : l % 512 < 512 := Nat.mod_lt _ (by norm_num)

theorem GL_eq {l y : Nat} (hl : l < 262144) (hy : y < 31671) :
    CFSG.KD.Fi23Y.GL l y = actN (lvP l) y := by
  have e1 : Nat.shiftRight l (nat_lit 9) = l / 512 := Nat.shiftRight_eq_div_pow l 9
  have e2 : Nat.land l (nat_lit 511) = l % 512 := Nat.and_two_pow_sub_one_eq_mod l 9
  unfold CFSG.KD.Fi23Y.GL lvP
  rw [e1, e2, gK_eq (leaf_hi_lt hl) (leaf_lo_lt l) hy]

theorem GL_lt {l y : Nat} (hl : l < 262144) (hy : y < 31671) : CFSG.KD.Fi23Y.GL l y < 31671 := by
  rw [GL_eq hl hy]
  exact actN_lt _ hy

theorem CD_eq (l : Nat) : CFSG.KD.Fi23Y.CD l = code (l / 512) (l % 512) := by
  unfold CFSG.KD.Fi23Y.CD code
  congr 1
  change l = l / 512 * 512 + l % 512
  omega

theorem lvP_mem {l : Nat}
    (hl : l < 262144) : lvP l ∈ Xc :=
  leaf_mem (leaf_hi_lt hl) (leaf_lo_lt l)

theorem tv_Gs {i k : Nat} (hi : i < 2) (hk : k < 512) :
    tv i k ∈ CFSG.KS.PCC.Gs TY (bF (by norm_num) BS) i :=
  tw_mem syl_hyp (by norm_num) hi k hk

theorem tv_TY {i k : Nat} (hi : i < 2) (hk : k < 512) : tv i k ∈ TY :=
  ((CFSG.KS.PCC.mem_Gs i _).1 (tv_Gs hi hk)).1

theorem lvP_TY {l : Nat} (hl : l < 262144) : lvP l ∈ TY :=
  Subgroup.mul_mem _ (tv_TY (by norm_num) (leaf_hi_lt hl)) (tv_TY (by norm_num) (leaf_lo_lt l))

theorem TY_le : TY ≤ Xc := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, rfl⟩
  exact T23_le (sig_T23 l.isLt)

theorem tv1_zero {j : Nat} (hj : j < 512) : actN (tv 1 j) 0 = 0 := by
  have h := ((CFSG.KS.PCC.mem_Gs 1 _).1 (tv_Gs (i := 1) (by norm_num) hj)).2 0 (by norm_num)
  have e : (bF (n := 31671) (by norm_num) BS 0 : Fin 31671) = ⟨0, by norm_num⟩ := Fin.ext rfl
  rw [e] at h
  rw [actN_of_lt _ (by norm_num), h]

theorem tv_pt0 {k : Nat} (hk : k < 512) : actN (tv 0 k) 0 = r32 (TTS 0 0) k :=
  tw_pt syl_hyp (i := 0) (by norm_num) k hk

theorem tv_pt1 {k : Nat} (hk : k < 512) : actN (tv 1 k) 2 = r32 (TTS 1 0) k :=
  tw_pt syl_hyp (i := 1) (by norm_num) k hk

theorem pts_inj {i a b : Nat} (hi : i < 2) (ha : a < 512) (hb : b < 512)
    (e : r32 (TTS i 0) a = r32 (TTS i 0) b) : a = b :=
  (rep_of syl_hyp hi).inj ha hb e

theorem lvP_inj {l l' : Nat} (hl : l < 262144) (hl' : l' < 262144) (e : lvP l = lvP l') :
    l = l' := by
  have hk : l / 512 = l' / 512 := by
    have h := congrArg (fun p => actN p 0) e
    simp only [lvP, actN_mul] at h
    rw [tv1_zero (leaf_lo_lt l), tv1_zero (leaf_lo_lt l'), tv_pt0 (leaf_hi_lt hl), tv_pt0 (leaf_hi_lt hl')] at h
    exact pts_inj (by norm_num) (leaf_hi_lt hl) (leaf_hi_lt hl') h
  have hj : l % 512 = l' % 512 := by
    have e' : tv 1 (l % 512) = tv 1 (l' % 512) := by
      unfold lvP at e
      rw [hk] at e
      exact mul_left_cancel e
    have h := congrArg (fun p => actN p 2) e'
    rw [tv_pt1 (leaf_lo_lt l), tv_pt1 (leaf_lo_lt l')] at h
    exact pts_inj (by norm_num) (leaf_lo_lt _) (leaf_lo_lt _) h
  omega

private noncomputable def gsY (j : Nat) : Xc :=
  if h : 2 * j < 42 then ⟨sig 31671 SL (2 * j), T23_le (sig_T23 h)⟩ else 1

private theorem SL_size : SL.size = 42 := syl_hyp.letters.1

private theorem idx_val (g : Xc) {x : Nat} (hx : x < 31671) :
    CFSG.Sporadic.Th.idx 31671 g x = actN (g : Equiv.Perm (Fin 31671)) x := by
  rw [CFSG.Sporadic.Th.idx_of_lt g hx, actN_of_lt _ hx]
  rfl

private theorem gsY_val {j : Nat} (h : 2 * j < 42) :
    (gsY j : Equiv.Perm (Fin 31671)) = sig 31671 SL (2 * j) := by
  simp only [gsY, dif_pos h]

private theorem rep_gsY : ∀ j < SL.size / 2, CFSG.Sporadic.Th.Rep 31671 SL[2 * j]! (gsY j) := by
  intro j hj x hx
  have h2 : 2 * j < 42 := by rw [SL_size] at hj; omega
  rw [idx_val _ hx, gsY_val h2, actN_sig syl_hyp h2 hx]
  exact syl_hyp.letters.2 _ h2 x hx

private theorem chainQ_size : chainQ.size = 6 := by
  have h := congrArg List.length syl_hyp.chk.1
  rw [Array.length_toList] at h
  exact h

private theorem chainQ_get {t : Nat} (ht : t < 6) : chainQ[t]! = t := by
  rw [CFSG.KS.PC.getElem!_eq_getD, syl_hyp.chk.1]
  interval_cases t <;> rfl

private theorem sep_Xc (g : Xc)
    (h : ∀ t < chainQ.size, CFSG.Sporadic.Th.idx 31671 g chainQ[t]! = chainQ[t]!) : g = 1 := by
  rw [chainQ_size] at h
  apply Subtype.ext
  refine one_of_fix g.2 fun b hb => ?_
  have := h b hb
  rw [chainQ_get hb, idx_val _ (by omega)] at this
  exact this

private theorem trees_size {l : Nat} (hl : l < 2) : (chainTrees 31671 SL sylBase)[l]!.pts.size = 512 := by
  rw [tt_get hl, pts_size]
  rfl

private theorem sylBase_size : sylBase.size = 2 := syl_hyp.base.1

theorem card_TY_le :
    Nat.card TY ≤ 262144 := by
  have hc := syl_chain.2 3
  have hF := CFSG.Perm.chain_facts (G := Xc) (n := 31671) rep_gsY sep_Xc hc
  obtain ⟨h2, hinv, -⟩ := CFSG.Perm.chainOK_parts hc
  have hrep := CFSG.Perm.rep_pairG rep_gsY h2 hinv
  have hcard : Nat.card (CFSG.Perm.levelGroup SL sylBase (CFSG.Perm.pairG gsY) 0) = 262144 := by
    rw [hF.2.2 0 (Nat.zero_le _), sylBase_size,
      show Finset.Ico 0 2 = {0, 1} by decide, Finset.prod_insert (by decide),
      Finset.prod_singleton, trees_size (l := 0) (by norm_num), trees_size (l := 1) (by norm_num)]
    norm_num
  have hle : TY ≤ (CFSG.Perm.levelGroup SL sylBase (CFSG.Perm.pairG gsY) 0).map Xc.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    have hl : l.val < SL.size := by rw [SL_size]; exact l.isLt
    refine ⟨CFSG.Perm.pairG gsY l.val, CFSG.Perm.lG_mem
      (CFSG.Perm.mem_levelLetters_zero.2 hl), ?_⟩
    apply perm_eq_of_act
    intro x hx
    change actN ((CFSG.Perm.pairG gsY l.val : Xc) : Equiv.Perm (Fin 31671)) x =
      actN (sig 31671 SL l.val) x
    rw [actN_sig syl_hyp l.isLt hx, ← idx_val _ hx, ← hrep l.val hl x hx,
      syl_hyp.letters.2 _ l.isLt x hx]
  calc Nat.card TY ≤ Nat.card ((CFSG.Perm.levelGroup SL sylBase (CFSG.Perm.pairG gsY) 0).map
        Xc.subtype) := Subgroup.card_le_of_le hle
    _ = Nat.card (CFSG.Perm.levelGroup SL sylBase (CFSG.Perm.pairG gsY) 0) :=
        Subgroup.card_map_of_injective Xc.subtype_injective
    _ = 262144 := hcard

theorem exists_leaf
    {b : Equiv.Perm (Fin 31671)} (hb : b ∈ TY) : ∃ l < 262144, b = lvP l := by
  let f : Fin 262144 → TY := fun l => ⟨lvP l.val, lvP_TY l.isLt⟩
  have hf : Function.Injective f := fun a c e =>
    Fin.ext (lvP_inj a.isLt c.isLt (congrArg Subtype.val e))
  have hbij := hf.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact card_TY_le)
  obtain ⟨l, hl⟩ := hbij.2 ⟨b, hb⟩
  exact ⟨l.val, l.isLt, (congrArg Subtype.val hl).symm⟩

theorem card_TY :
    Nat.card TY = 2 ^ 18 := by
  refine le_antisymm (by rw [show (2 : Nat) ^ 18 = 262144 by norm_num]; exact card_TY_le) ?_
  have h := card_ge syl_hyp (by norm_num)
  have e : ((List.range 2).map CNTS).prod = 2 ^ 18 := by rfl
  rw [e] at h
  exact h

end CertificateChecks.KernelFi23Y.KSY

end
