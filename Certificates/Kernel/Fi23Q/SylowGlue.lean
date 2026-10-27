
module

public import Certificates.Kernel.Fi23Q.CensusGlue
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
public import Certificates.Kernel.Fi23Q.ChainDefs
import CFSG.Certificates.Kernel.Fi23Q.ChainSound
import Certificates.Kernel.Fi23Q.ChainChk

public section

namespace CertificateChecks.KernelFi23Q

open CFSG.Sporadic.Fi23 CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KS.Pc3 CFSG.KS.Fi23Q
  CFSG.Perm CFSG.KD.Fi23K
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (qG factorization_three_pow_mul)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow (pcSub pc_card_le)

open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem aE_mem_Q :
    ∀ k < 13, aE k ∈ Subgroup.closure (qG '' Set.Iio 3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h13
    by_cases h3 : k < 3
    · rw [aE_lt3 h3]
      exact Subgroup.subset_closure ⟨k, h3, rfl⟩
    have hk3 : 3 ≤ k := by omega
    have hi := ih _ (cI_lt hk3) (by have := cI_lt hk3; omega)
    have hj : qG (CFSG.KD.Fi23Q.cJ k) ∈ Subgroup.closure (qG '' Set.Iio 3) :=
      Subgroup.subset_closure ⟨_, cJ_lt k, rfl⟩
    rw [aE_comm hk3 h13]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hi)
      (Subgroup.inv_mem _ hj)) hi) hj

theorem closure_aE_eq :
    Subgroup.closure (aE '' Set.Iio 13) = Subgroup.closure (qG '' Set.Iio 3) := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) qG_closure_le
  rintro _ ⟨k, hk, rfl⟩
  exact aE_mem_Q k hk

theorem nv_mem (v : ℕ) :
    nv aE 13 v ∈ Subgroup.closure (aE '' Set.Iio 13) := by
  unfold nv
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  have hk' : aE k ∈ aE '' Set.Iio 13 := ⟨k, List.mem_range.1 hk, rfl⟩
  exact Subgroup.pow_mem _ (Subgroup.subset_closure hk') _

theorem lowV_eq (u k : ℕ) : lowV u k = u % 4 ^ k := by
  change u &&& ((1 <<< (k <<< 1)) - 1) = _
  rw [Nat.shiftLeft_eq 1 (k <<< 1), one_mul, Nat.and_two_pow_sub_one_eq_mod, pow4]

theorem dg_zero_of_mod {c j : ℕ} (h : c % 4 ^ j = 0) {m : ℕ} (hm : m < j) : dg c m = 0 := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  rw [dg_eq, show (4 : ℕ) ^ j = 4 ^ m * (4 * 4 ^ (j - 1 - m)) by
      rw [← pow_succ', ← pow_add]; congr 1; omega,
    mul_assoc, Nat.mul_div_cancel_left _ (by positivity), mul_assoc, Nat.mul_mod_right]

theorem nv_mem_tail {w i : ℕ} (hw : ∀ m ≤ i, dg w m = 0) :
    nv aE 13 w ∈ Subgroup.closure (aE '' {k | i + 1 ≤ k ∧ k < 13}) := by
  unfold nv
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  have hk' := List.mem_range.1 hk
  by_cases hki : k ≤ i
  · rw [hw k hki, pow_zero]
    exact Subgroup.one_mem _
  · have hm : aE k ∈ aE '' {k | i + 1 ≤ k ∧ k < 13} := ⟨k, ⟨by omega, hk'⟩, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.subset_closure hm) _

@[expose] noncomputable def qa (i : Fin 13) :
    Subgroup.closure (aE '' Set.Iio 13) :=
  ⟨(aE i)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, i.isLt, rfl⟩)⟩

theorem mem_pcSub (j : ℕ) (y : Subgroup.closure (aE '' Set.Iio 13))
    (hy : (y : CFSG.Sporadic.Fi23.J) ∈ Subgroup.closure (aE '' {k | j ≤ k ∧ k < 13})) : y ∈ pcSub qa j := by
  have hle : Subgroup.closure (aE '' {k | j ≤ k ∧ k < 13}) ≤
      (pcSub qa j).map (Subgroup.closure (aE '' Set.Iio 13)).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, ⟨hjk, hk⟩, rfl⟩
    refine ⟨(qa ⟨k, hk⟩)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨k, hk⟩, hjk, rfl⟩), ?_⟩
    simp [qa]
  obtain ⟨z, hz, e⟩ := Subgroup.mem_map.1 (hle hy)
  have hzy : z = y := Subtype.ext e
  rwa [← hzy]

theorem qa_gen : Subgroup.closure (Set.range qa) = ⊤ := by
  rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage, Subgroup.closure_le]
  rintro y ⟨k, hk, e⟩
  have hy : y = (qa ⟨k, hk⟩)⁻¹ := Subtype.ext (by simp [qa, e])
  rw [hy]
  exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, rfl⟩)

theorem card_Qa_le :
    Nat.card (Subgroup.closure (aE '' Set.Iio 13)) ≤ 3 ^ 13 := by
  have hd := relK_parts.1
  have hP := pcRel aE aE_acts
  unfold pcDataOK at hd
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff,
    CFSG.KS.PK.strictB_eq] at hd
  refine (pc_card_le (p := 3) (by norm_num) qa qa_gen (fun i => ?_) (fun i j hij => ?_)).2
  · apply mem_pcSub
    have hw := (hd.2 i i.isLt).2.1
    rw [lowV_eq] at hw
    have hw' := Nat.eq_of_beq_eq_true hw
    have e : (((qa i) ^ 3 : Subgroup.closure (aE '' Set.Iio 13)) : CFSG.Sporadic.Fi23.J) =
        (nv aE 13 (f32 CFSG.KD.Fi23Q.PW i))⁻¹ := by
      rw [SubgroupClass.coe_pow, qa, inv_pow, hP.cube i i.isLt]
    rw [e]
    exact Subgroup.inv_mem _ (nv_mem_tail fun m hm => dg_zero_of_mod hw' (by omega))
  · apply mem_pcSub
    have hj13 := j.isLt
    have hij' : i.val < j.val := hij
    have hcj := (hd.2 i i.isLt).2.2 j hj13
    simp only [CFSG.KS.PK.bIf_eq, Nat.blt_eq, hij', ↓reduceIte, CFSG.KS.PK.strictB_eq,
      CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, cj_index] at hcj
    have hc := Nat.eq_of_beq_eq_true hcj.2
    have h4 : Nat.shiftLeft 1 (Nat.shiftLeft j.val 1) = 4 ^ j.val := by
      change 1 <<< (j.val <<< 1) = _
      rw [Nat.shiftLeft_eq 1, one_mul, pow4]
    rw [lowV_eq, h4] at hc
    have hc' : f32 CFSG.KD.Fi23Q.CJ (16 * i + j) % 4 ^ j.val = 0 := by
      rw [← Nat.mod_mod_of_dvd _ (pow_dvd_pow 4 (Nat.le_succ j.val)), hc, Nat.mod_self]
    have e : ((qa i * qa j * (qa i)⁻¹ : Subgroup.closure (aE '' Set.Iio 13)) : CFSG.Sporadic.Fi23.J) =
        (nv aE 13 (f32 CFSG.KD.Fi23Q.CJ (16 * i + j)))⁻¹ := by
      rw [← hP.conj i j hij' hj13]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, qa]
      group
    rw [e]
    exact Subgroup.inv_mem _ (nv_mem_tail fun m hm => dg_zero_of_mod hc' (by omega))

@[expose] noncomputable def chainE : List (ℕ × List CFSG.Sporadic.Fi23.J) :=
  CFSG.KD.Fi23Q.chainL.map fun l => (l.1, l.2.map (nv aE 13))

theorem le_card_Qa :
    3 ^ 13 ≤ Nat.card (Subgroup.closure (aE '' Set.Iio 13)) := by
  have hW : ∀ v, vecOK 13 v = true → ∀ x < 31671,
      imgV CFSG.KD.Fi23Q.H 13 v x = idx 31671 (nv aE 13 v) x := by
    intro v hv x hx
    obtain ⟨W1, W2⟩ := nwR_spec aE (vecOK_dg hv)
    rw [← W1]
    exact wvH_eq aE aE_acts W2 hx
  have hC := (chainP_of (act := idx 31671) hW CFSG.KD.Fi23Q.chainL CFSG.KD.Fi23Q.chainK_ok).1
  have hN := prs_nodup (fun g h x => idx_mul g h x) (fun x => idx_one x) _ hC
  have hlen : (prs (chainE.map Prod.snd)).length = 3 ^ 13 := by
    rw [length_prs, chainE, List.map_map, List.map_map]
    simp only [Function.comp_def, List.length_map]
    decide +kernel
  rw [← hlen]
  refine length_le_card _ hN (prs_mem _ _ ?_)
  intro L hL x hx
  rw [chainE, List.map_map, List.mem_map] at hL
  obtain ⟨l, -, rfl⟩ := hL
  simp only [Function.comp_apply] at hx
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
  exact nv_mem v

theorem card_Q :
    Nat.card (Subgroup.closure (qG '' Set.Iio 3)) = 3 ^ 13 := by
  rw [← closure_aE_eq]
  exact le_antisymm card_Qa_le le_card_Qa

theorem exists_sylow_Q :
    ∃ P : Sylow 3 CFSG.Sporadic.Fi23.J, (P : Subgroup CFSG.Sporadic.Fi23.J) = Subgroup.closure (qG '' Set.Iio 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Subgroup.closure (qG '' Set.Iio 3)) = 3 ^ (Nat.card CFSG.Sporadic.Fi23.J).factorization 3 := by
    rw [card_Q, card_J, show (4089470473293004800 : ℕ) = 3 ^ 13 * 2565020057600 by norm_num,
      factorization_three_pow_mul 13 _ (by norm_num)]
  exact ⟨Sylow.ofCard _ hcard, Sylow.coe_ofCard _ _⟩

theorem orderOf_three_J
    {s : CFSG.Sporadic.Fi23.J} (hs : orderOf s = 3) : ∃ c : Fin 4, IsConj s (t3 c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := exists_sylow_Q
  have hsp : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨P, hP⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CFSG.Sporadic.Fi23.J P T
  have hsT : g * s * g⁻¹ ∈ (T : Subgroup CFSG.Sporadic.Fi23.J) := by
    have h1 : s ∈ (P : Subgroup CFSG.Sporadic.Fi23.J) := hP (Subgroup.mem_zpowers s)
    have h2 : MulAut.conj g s ∈ (MulAut.conj g • (P : Set CFSG.Sporadic.Fi23.J)) := Set.smul_mem_smul_set h1
    rw [← Sylow.coe_smul, hg] at h2
    have h3 : g * s * g⁻¹ ∈ T := by simpa [MulAut.conj_apply] using h2
    exact h3
  rw [hT] at hsT
  have ho : orderOf (g * s * g⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
  obtain ⟨c, hc⟩ := orderOf_three_Q hsT ho
  exact ⟨c, (isConj_iff.2 ⟨g, rfl⟩).trans hc⟩

end CertificateChecks.KernelFi23Q

end
