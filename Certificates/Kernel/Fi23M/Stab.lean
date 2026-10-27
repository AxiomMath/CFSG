module

public import Certificates.Kernel.Fi23K.Iso
public import CFSG.Certificates.Kernel.Spor.PChainLower
import Certificates.Kernel.Fi23K.Misc
import Certificates.Kernel.Fi23K.Tree0
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import CFSG.Certificates.Kernel.Spor.ONKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.KD.Fi23K CFSG.KC.Fi23K CFSG.KS.PC CFSG.KS.PCC CFSG.KC.Enum CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.KS.TBfs CFSG.KS.PEnum

theorem hn : 0 < 31671 := by norm_num

local notation "sg" => sig 31671 (chainLetters orbLit)

noncomputable abbrev H1 : Subgroup (Equiv.Perm (Fin 31671)) :=
  Subgroup.closure (sg '' {l | l ∈ lvK LL BB 24 1})

theorem lv_one {i l : ℕ} (hi : 1 ≤ i) (hl : l ∈ lvK LL BB 24 i) : l ∈ lvK LL BB 24 1 := by
  rw [mem_lvK] at hl ⊢
  exact ⟨hl.1, fun j hj => hl.2 j (by omega)⟩

theorem letter_Gs1 {j l : ℕ} (hj : j + 1 < 6) (hl : l ∈ lvK LL BB 24 (j + 1)) :
    sg l ∈ Gs H1 (fun i => bF hn BB (i + 1)) j := by
  have hl' := mem_lvK.1 hl
  rw [mem_Gs]
  refine ⟨Subgroup.subset_closure ⟨l, lv_one (by omega) hl, rfl⟩, fun k hk => Fin.ext ?_⟩
  beta_reduce
  rw [sig_val chain_hyp hl'.1, bF_val chain_hyp hn (by omega), hl'.2 (k + 1) (by omega)]

theorem tw_mem1 {j : ℕ} (hj : j + 1 < 6) : ∀ k < CNT (j + 1),
    twL 31671 (chainLetters orbLit) PARJ LABJ (j + 1) k ∈ Gs H1 (fun i => bF hn BB (i + 1)) j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PARJ (j + 1)) k < k
    · rw [ite_eq_left hc]
      exact Subgroup.mul_mem _ (letter_Gs1 hj (lab_mem chain_hyp hj hk hc.1)) (ih _ hc.2 (by omega))
    · rw [ite_eq_right hc]
      exact Subgroup.one_mem _

theorem dSet_sub1 {j : ℕ} (hj : j + 1 < 6) :
    (↑(dSet hn CNT PTSJ (j + 1)) : Set (Fin 31671)) ⊆
      MulAction.orbit (Gs H1 (fun i => bF hn BB (i + 1)) j) (bF hn BB (j + 1)) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_range] at hk
  refine mem_orbit_Gs.2 ⟨_, tw_mem1 hj k hk, Fin.ext ?_⟩
  rw [← actN_fin, bF_val chain_hyp hn hj, tw_pt chain_hyp hj k hk]
  exact (Nat.mod_eq_of_lt ((rep_of chain_hyp hj).pt k hk).lt).symm

theorem prod_cnt1 : ∏ l ∈ Finset.range 5, CNT (l + 1) = 129123503308800 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  decide +kernel

theorem card_H1 : 129123503308800 ≤ Nat.card H1 := by
  rw [card_chain H1 (fun i => bF hn BB (i + 1)) 5, ← prod_cnt1]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ Nat.card_pos)
  refine Finset.prod_le_prod' fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [← dSet_card chain_hyp hn (l := l + 1) (by omega), ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (dSet_sub1 (by omega)) (Set.toFinite _)

theorem card_Gs1 :
    Nat.card (Gs T23 (bF hn BB) 1) ≤ 129123503308800 := by
  have hc := card_chain T23 (bF hn BB) 1
  rw [Finset.prod_range_one] at hc
  have h0 := Set.ncard_le_ncard (dSet_sub_orbit chain_hyp hn (l := 0) (by norm_num))
    (Set.toFinite _)
  rw [Set.ncard_coe_finset, dSet_card chain_hyp hn (by norm_num)] at h0
  have hT : Nat.card T23 = 4089470473293004800 := by rw [grp_eq]; exact card_Xc_eq
  have e0 : CNT 0 = 31671 := rfl
  rw [e0] at h0
  rw [hT] at hc
  have : 31671 * Nat.card (Gs T23 (bF hn BB) 1) ≤ 31671 * 129123503308800 := by
    calc 31671 * Nat.card (Gs T23 (bF hn BB) 1)
        ≤ (MulAction.orbit (Gs T23 (bF hn BB) 0) (bF hn BB 0)).ncard *
          Nat.card (Gs T23 (bF hn BB) 1) := Nat.mul_le_mul_right _ h0
      _ = 31671 * 129123503308800 := by rw [← hc]
  omega

theorem H1_le : H1 ≤ Gs T23 (bF hn BB) 1 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact sig_mem_Gs chain_hyp hn (by norm_num) hl

theorem stab_eq : H1 = Gs T23 (bF hn BB) 1 :=
  Subgroup.eq_of_le_of_card_ge H1_le (card_Gs1.trans card_H1)

theorem stab_mem {p : Equiv.Perm (Fin 31671)} (hp : p ∈ Xc)
    (h0 : p ⟨0, hn⟩ = ⟨0, hn⟩) : p ∈ H1 := by
  rw [stab_eq, mem_Gs]
  refine ⟨by rw [grp_eq]; exact hp, fun k hk => ?_⟩
  have e : bF hn BB k = ⟨0, hn⟩ := by
    apply Fin.ext
    rw [bF_val chain_hyp hn (by omega)]
    change k = 0
    omega
  rw [e, h0]

theorem lv1_eq : lvK LL BB 24 1 = List.range' 4 20 := by decide +kernel

theorem misc_eqs : ∀ j < 10, EL (138 + j) = [43, 52 + (4 + 2 * j)] ∧
    ER (138 + j) = [52 + (4 + 2 * j), 43] := by
  decide +kernel

theorem sg_acts {l : ℕ} (hl : l < 24) : ActsAs (sg l) (LL l) :=
  fun x hx => sig_val chain_hyp hl ⟨x, hx⟩

theorem comm_reg {l k : ℕ} (hl : l < 24) (hk : k < 150) (hL : EL k = [43, 52 + l])
    (hR : ER k = [52 + l, 43]) {q : Equiv.Perm (Fin 31671)} (hq : ActsAs q (tb G 43)) :
    sg l * q = q * sg l := by
  have h1 := (sg_acts hl).mul hq
  have h2 := hq.mul (sg_acts hl)
  refine ActsAs.ext h1 (fun x hx => ?_)
  rw [h2 x hx]
  have h := eqv hk hx
  rw [hL, hR] at h
  simp only [wv_cons, wv_nil] at h
  unfold LL
  exact h

theorem sg_inv {j : ℕ} (hj : j < 12) : sg (2 * j + 1) * sg (2 * j) = 1 := by
  have h1 := (sg_acts (l := 2 * j + 1) (by omega)).mul (sg_acts (l := 2 * j) (by omega))
  refine ActsAs.ext h1 (fun x hx => ?_)
  exact (letter_inv hj hx).symm

theorem comm_even {j : ℕ} (hj : j < 10) {q : Equiv.Perm (Fin 31671)} (hq : ActsAs q (tb G 43)) :
    sg (2 * (j + 2)) * q = q * sg (2 * (j + 2)) := by
  obtain ⟨hL, hR⟩ := misc_eqs j hj
  have e : 4 + 2 * j = 2 * (j + 2) := by omega
  rw [e] at hL hR
  exact comm_reg (by omega) (by omega) hL hR hq

theorem comm_lv1 {l : ℕ} (hl : l ∈ {l | l ∈ lvK LL BB 24 1}) {q : Equiv.Perm (Fin 31671)}
    (hq : ActsAs q (tb G 43)) : sg l * q = q * sg l := by
  have hl0 : l ∈ lvK LL BB 24 1 := hl
  rw [lv1_eq, List.mem_range'_1] at hl0
  obtain ⟨j, hj, h | h⟩ : ∃ j < 10, l = 2 * (j + 2) ∨ l = 2 * (j + 2) + 1 :=
    ⟨(l - 4) / 2, by omega, by omega⟩
  · rw [h]
    exact comm_even hj hq
  · rw [h]
    have hc : Commute (sg (2 * (j + 2))) q := comm_even hj hq
    have hinv : sg (2 * (j + 2) + 1) = (sg (2 * (j + 2)))⁻¹ :=
      eq_inv_of_mul_eq_one_left (sg_inv (by omega))
    rw [hinv]
    exact (Commute.inv_left hc).eq

theorem H1_comm {q : Equiv.Perm (Fin 31671)} (hq : ActsAs q (tb G 43)) :
    ∀ p ∈ H1, p * q = q * p := by
  have hle : H1 ≤ Subgroup.centralizer {q} := by
    rw [Subgroup.closure_le]
    intro p hp
    obtain ⟨l, hl, hpl⟩ := hp
    rw [← hpl, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact comm_lv1 hl hq
  intro p hp
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hp)

end CertificateChecks.KernelFi23M

end
