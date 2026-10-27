
module

public import Certificates.Kernel.F4Gamma.Words
public import Certificates.Kernel.F4Gamma.Flag
public import Certificates.Kernel.F4Syl3.PhiInv
public import CFSG.Certificates.Kernel.F4Gamma.Sound
import all CFSG.LieType.Simplicity.TitsBits
import all CFSG.Certificates.Kernel.F4SaltSound

public section

namespace CFSG.KC.F4Gamma

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.KC.F4Salt CFSG.KC.F4Rank CFSG.KC.F4Syl3 CFSG.KD.F4Gamma
open CFSG.RankThree.PartTwo.Sec21.FF81.F4 (invClosure finite_adj wordOfCodes_flip flipCode)
open CFSG.RankThree.PartOne.SEITZX (wordOfCodes)

section Gens

variable {K : Type} [Field K]

variable (K) in
noncomputable def gK (k : ℕ) : adjointGroup ReeTag.F4.tag K :=
  evalG K (wordOfCodes (decW8 (ws.getD k 0) (ls.getD k 0)))

variable (K) in
noncomputable def gSet : Set (adjointGroup ReeTag.F4.tag K) :=
  gK K '' {k | k < 3}

theorem hasBits_of_eqS {g : adjointGroup ReeTag.F4.tag K} {A G : ℕ} (hg : HasBitsS K g A)
    (h : eqS A (saltOf G) = true) : HasBits K g G := by
  have h1 := (eqS_iff A (saltOf G)).1 h
  rw [dataS_saltOf] at h1
  unfold HasBitsS HasBits at hg
  unfold HasBits
  rw [hg]
  exact (toEnd_eq_toEnd_iff _ _).2 h1

theorem word_ok : ∀ k < 3, eqS (wordS (ws.getD k 0) (ls.getD k 0)) (saltOf (gs.getD k 0)) = true ∧
    eqS (wordS (fs.getD k 0) (ls.getD k 0)) (saltOf (gs.getD k 0)) = true
  | 0, _ => ⟨word0_ok, flip0_ok⟩
  | 1, _ => ⟨word1_ok, flip1_ok⟩
  | 2, _ => ⟨word2_ok, flip2_ok⟩
  | n + 3, h => absurd h (by omega)

variable [CharP K 2]

theorem hasBits_gK {k : ℕ} (hk : k < 3) : HasBits K (gK K k) (gs.getD k 0) :=
  hasBits_of_eqS (hasBitsS_wordS _ _) (word_ok k hk).1

theorem endOf_gK {k : ℕ} (hk : k < 3) : endOf (gK K k) = toEnd K (gs.getD k 0) :=
  hasBits_gK (K := K) hk

end Gens

theorem gK_mem_reeFixed {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {k : ℕ}
    (hk : k < 3) : gK K k ∈ reeFixed ReeTag.F4 K 0 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hf : decW8 (fs.getD k 0) (ls.getD k 0) =
      (decW8 (ws.getD k 0) (ls.getD k 0)).map flipCode :=
    decW8_of_flipOK (allN_true flip_ok k hk)
  have hflip : HasBits K (evalG K (wordOfCodes (decW8 (fs.getD k 0) (ls.getD k 0))))
      (gs.getD k 0) := hasBits_of_eqS (hasBitsS_wordS _ _) (word_ok k hk).2
  rw [mem_reeFixed, gK, reeAut_evalG, ← wordOfCodes_flip _ (decW8_lt _ _), ← hf]
  exact ((hflip.eq_iff (hasBits_gK hk)).2 rfl)

section Gens2

variable {K : Type} [Field K] [CharP K 2]

theorem gSet_spec : ∀ s ∈ gSet K, FlagP K bb (endOf s) ∧
    formR K lam (endOf s (bitVec K (col bb 49))) = formR K mu (endOf s (bitVec K (col bb 50))) := by
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < 3 := hk
  rw [endOf_gK hk']
  refine ⟨flagP_of_flagChk (allN_true flag_ok k hk'), ?_⟩
  rw [toEnd_bitVec, toEnd_bitVec, formR_bitVec, formR_bitVec, ← colR_eq, ← colR_eq,
    beq_iff_eq.1 (allN_true chi_ok k hk')]

theorem chi_gK_zero : formR K lam (endOf (gK K 0) (bitVec K (col bb 49))) = 1 := by
  rw [endOf_gK (by norm_num), toEnd_bitVec, formR_bitVec, ← colR_eq, chi_one, Nat.cast_one]

variable (K) in
noncomputable def stabElt (j : ℕ) : adjointGroup ReeTag.F4.tag K :=
  ((hw.getD j []).map (gK K)).prod

theorem stabElt_spec {j : ℕ} (hj : j < 3) : (stabElt K j ∈ Subgroup.closure (gSet K) ∧
    endOf (stabElt K j) (bitVec K w1) = bitVec K w1) ∧ HasBits K (stabElt K j) (hs.getD j 0) := by
  have hr := allN_true stab_ok j hj
  simp only [stabRow, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, beq_iff_eq] at hr
  obtain ⟨⟨hlt, heq⟩, hfix⟩ := hr
  rw [gs_length] at hlt
  have hb : HasBits K (stabElt K j) (hs.getD j 0) :=
    hasBits_of_eqS (hasBitsS_prodS _ fun k hk => hasBits_gK (hlt k hk)) heq
  refine ⟨⟨list_prod_mem fun x hx => ?_, ?_⟩, hb⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨k, hlt k hk, rfl⟩
  · change ((stabElt K j : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) _ = _
    rw [hb, toEnd_bitVec, hfix]

end Gens2

theorem factorization_two_card_Gamma' : (35942400 : ℕ).factorization 2 = 12 := by
  have h : (35942400 : ℕ) = 2 ^ 12 * 8775 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem gamma_sylow2_kc (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2) :
    ∃ V₀ : Subgroup (adjointGroup ReeTag.F4.tag K),
      CFSG.RankThree.PartTwo.Sec21.FF79.IsSylowOf 2 V₀ (reeFixed ReeTag.F4 K 0) ∧
        invClosure V₀ ≠ V₀ := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup ReeTag.F4.tag K) := finite_adj
  have hVΓ : Subgroup.closure (gSet K) ≤ reeFixed ReeTag.F4 K 0 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact gK_mem_reeFixed hk
  have hΓ : Nat.card (reeFixed ReeTag.F4 K 0) = 2 ^ 12 * 8775 := by
    rw [CFSG.RankThree.PartTwo.Census.Carrier.Tits.card_reeFixed hK]
    norm_num
  have hF := flagP_closure (K := K) basis_ok fun s hs => (gSet_spec s hs).1
  have h64 : ∀ x ∈ Subgroup.closure (gSet K), x ^ 64 = 1 := fun x hx =>
    pow64_of_flagP basis_ok (hF x hx)
  have hgs : ∀ k < gs.length, ∃ s ∈ Subgroup.closure (gSet K), HasBits K s (gs.getD k 0) := by
    intro k hk
    rw [gs_length] at hk
    exact ⟨gK K k, Subgroup.subset_closure ⟨k, hk, rfl⟩, hasBits_gK hk⟩
  have hhs : ∀ j < hs.length, ∃ s, (s ∈ Subgroup.closure (gSet K) ∧
      endOf s (bitVec K w1) = bitVec K w1) ∧ HasBits K s (hs.getD j 0) := by
    intro j hj
    rw [hs_length] at hj
    exact ⟨stabElt K j, stabElt_spec hj⟩
  have hcard := card_eq_of_pow64 hVΓ hΓ h64 (card_ge_of_orbits hgs hhs orb1_ok orb2_ok)
  refine ⟨Subgroup.closure (gSet K),
    CFSG.RankThree.PartTwo.Sec21.FF79.L41.isSylowOf_of_card_p hVΓ ?_,
    invClosure_ne_of_flag basis_ok lam_ok mu_ok gSet_spec ⟨0, by norm_num, rfl⟩ chi_gK_zero⟩
  rw [hcard, CFSG.RankThree.PartTwo.Census.Carrier.Tits.card_reeFixed hK,
    factorization_two_card_Gamma']
  norm_num

end CFSG.KC.F4Gamma

end
