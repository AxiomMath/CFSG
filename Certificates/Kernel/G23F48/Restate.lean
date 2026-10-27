module

public import Certificates.Kernel.G23F48.PtsGlue
public import Certificates.Kernel.G23F48.LetterGlue
public import Certificates.Kernel.G23F48.A24Max

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KD.G23A22
open CFSG.Sporadic.HNOddCore (arrGen)

open Certificates in
open CFSG CFSG.ASVolI in
theorem facts7760 : (∀ i < 728, ((burnsideF48t_g23Pts ())[i]!).size = 14 ∧
      (((burnsideF48t_g23Pts ())[i]!).all fun x => decide (x < 3)) = true ∧
      ((burnsideF48t_g23Pts ())[i]!).find? (· != 0) = some 1) ∧
    (∀ i < 728, ∀ l < 728, (burnsideF48t_g23Pts ())[i]! = (burnsideF48t_g23Pts ())[l]! → i = l) ∧
    (∀ i < 728, ∀ l < 728,
      (burnsideF48t_g23Pts ())[i]! ≠ ((burnsideF48t_g23Pts ())[l]!).map fun x => 2 * x % 3) ∧
    ∀ k < 4, ∀ i : Fin 728, (burnsideF48t_g23Pts ())[((burnsideF48t_g23γ k i : Fin 728) : ℕ)]! =
      burnsideF48t_g23Norm
        (burnsideF48t_g23MulVec (burnsideF48t_g23Mats ())[k]! (burnsideF48t_g23Pts ())[(i : ℕ)]!) := by
  refine ⟨fun i hi => pts_basic hi, fun i hi l hl h => pts_inj hi hl h,
    fun i hi l hl => pts_ne_two hi hl, fun k hk i => ?_⟩
  have e : burnsideF48t_g23γ k = gam k := rfl
  rw [e, ← (prep_gen hk).1 i]
  exact (pts_gen hk i.2).2

theorem ab_mem_B : sig 0 ∈ arrGen 728 burnsideF48t_g23BArr ∧ sig 1 ∈ arrGen 728 burnsideF48t_g23BArr :=
  ⟨sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num),
    sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num)⟩

theorem P1_closure : burnsideF48t_g23P1' =
    Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1, burnsideF48t_g23σ 2} := by
  refine le_antisymm (arrGen_letters_le id fun k hk => ?_) ?_
  · have hk3 : k < 3 := hk
    interval_cases k
    · exact ⟨by norm_num, rfl, Subgroup.subset_closure (by simp [sig_eq])⟩
    · exact ⟨by norm_num, rfl, Subgroup.subset_closure (by simp [sig_eq])⟩
    · exact ⟨by norm_num, rfl, Subgroup.subset_closure (by simp [sig_eq])⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num)
    · exact sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num)
    · exact sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num)

theorem P2_closure : burnsideF48t_g23P2' =
    Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1, burnsideF48t_g23σ 3} := by
  refine le_antisymm (arrGen_letters_le (fun k => k + k / 2) fun k hk => ?_) ?_
  · have hk3 : k < 3 := hk
    interval_cases k
    · exact ⟨by norm_num, rfl, Subgroup.subset_closure (by simp [sig_eq])⟩
    · exact ⟨by norm_num, rfl, Subgroup.subset_closure (by simp [sig_eq])⟩
    · exact ⟨by norm_num, rfl, Subgroup.subset_closure (by simp [sig_eq])⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num)
    · exact sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num)
    · exact sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num)

theorem B_closure : burnsideF48t_g23B' =
    Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1} := by
  refine le_antisymm (arrGen_letters_le id fun k hk => ?_) ?_
  · have hk2 : k < 2 := hk
    interval_cases k
    · exact ⟨by norm_num, rfl, Subgroup.subset_closure (by simp [sig_eq])⟩
    · exact ⟨by norm_num, rfl, Subgroup.subset_closure (by simp [sig_eq])⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [ab_mem_B.1, ab_mem_B.2]

open Certificates in
open CFSG CFSG.ASVolI in
theorem facts7762 : burnsideF48t_g23X = Subgroup.closure (Set.range fun i : Fin 4 => burnsideF48t_g23γ i) ∧
    burnsideF48t_g23P1' =
      Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1, burnsideF48t_g23σ 2} ∧
    burnsideF48t_g23P2' =
      Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1, burnsideF48t_g23σ 3} ∧
    burnsideF48t_g23B' = Subgroup.closure {burnsideF48t_g23σ 0, burnsideF48t_g23σ 1} ∧
    (∀ i < 4, burnsideF48t_g23σ i ∈ burnsideF48t_g23X) ∧
    (∀ i < 4, burnsideF48t_g23τ * burnsideF48t_g23γ i * burnsideF48t_g23τ⁻¹ ∈ burnsideF48t_g23X) ∧
    burnsideF48t_g23S0' ≤ burnsideF48t_g23B' ∧ burnsideF48t_g23K' ≤ burnsideF48t_g23B' ∧
    (∀ r ∈ burnsideF48t_g23R1 ++ burnsideF48t_g23R2 ++
      [(List.replicate 6 [((2 : Fin 4), true), ((3 : Fin 4), true)]).flatten],
      burnsideF48s_ev (fun i : Fin 4 => burnsideF48t_g23σ i) r = 1) ∧
    (¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * burnsideF48t_g23κ 0 =
        burnsideF48t_g23κ 0 * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) ∧
      ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * burnsideF48t_g23κ 1 =
        burnsideF48t_g23κ 1 * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) ∧
      ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * (burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) =
        (burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) *
          (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3))) ∧
    364 ≤ ((burnsideF48t_g23τ 0 : Fin 728) : ℕ) ∧
    (burnsideF48t_g23σ 0 0 = 0 ∧ burnsideF48t_g23σ 0 364 = 364 ∧
      burnsideF48t_g23σ 1 0 = 0 ∧ burnsideF48t_g23σ 1 364 = 364 ∧
      burnsideF48t_g23σ 2 0 = 0 ∧ burnsideF48t_g23σ 3 364 = 364 ∧
      burnsideF48t_g23σ 3 0 ≠ 0 ∧ burnsideF48t_g23σ 2 364 ≠ 364) ∧
    (∀ s ∈ burnsideF48t_g23S0', s 0 = 0 ∧ s 364 = 364) ∧
    (∀ p : Fin 728, p ≠ 0 → p ≠ 364 → ∃ s ∈ burnsideF48t_g23S0', s p ≠ p) ∧
    (∀ p : Fin 728, 364 ≤ (p : ℕ) → ∃ g ∈ burnsideF48t_g23P1', g p ≠ p) ∧
    ∀ p : Fin 728, (p : ℕ) < 364 → ∃ g ∈ burnsideF48t_g23P2', g p ≠ p :=
  ⟨X_eq, P1_closure, P2_closure, B_closure, fun _ hi => sigma_mem_X hi,
    fun _ hi => tauConj_mem_X hi, S0_le recL ab_mem_B, K_le recL ab_mem_B, rels_hold, comm_xy,
    tau_zero_ge, letters_fix, fun _ hs => S0_fix hs, fun _ h0 h364 => S0_moves h0 h364,
    fun _ hp => P1_moves hp, fun _ hp => P2_moves hp⟩

theorem card_rest (hX : Nat.card ↥burnsideF48t_g23X = 4245696) :
    Nat.card ↥burnsideF48t_g23P1' = 11664 ∧ Nat.card ↥burnsideF48t_g23P2' = 11664 ∧
      Nat.card ↥burnsideF48t_g23B' = 2916 ∧ Nat.card ↥burnsideF48t_g23S0' = 729 ∧
      Nat.card ↥burnsideF48t_g23K' = 4 :=
  ⟨(card_P1_P2_B hX).1, (card_P1_P2_B hX).2.1, (card_P1_P2_B hX).2.2, card_S0, card_K⟩

open CFSG CFSG.ASVolI in
theorem facts7763 (hX : Nat.card ↥burnsideF48t_g23X = 4245696) : (∀ g ∈ burnsideF48t_g23X, ∀ x : Fin 728, (x : ℕ) < 364 → ((g x : Fin 728) : ℕ) < 364) ∧
    burnsideF48t_g23P1' =
      burnsideF48t_g23X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 728)) (0 : Fin 728) ∧
    burnsideF48t_g23P2' =
      burnsideF48t_g23X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 728)) (364 : Fin 728) ∧
    burnsideF48t_g23B' = burnsideF48t_g23P1' ⊓ burnsideF48t_g23P2' ∧
    (∀ R : Subgroup (Equiv.Perm (Fin 728)), burnsideF48t_g23P1' < R → R ≤ burnsideF48t_g23X →
      R = burnsideF48t_g23X) ∧
    (∀ R : Subgroup (Equiv.Perm (Fin 728)), burnsideF48t_g23P2' < R → R ≤ burnsideF48t_g23X →
      R = burnsideF48t_g23X) ∧
    burnsideF48t_g23B' ≤
      Subgroup.normalizer (burnsideF48t_g23S0' : Set (Equiv.Perm (Fin 728))) :=
  ⟨fun _ hg _ hx => X_lt hg hx, P1_eq hX, P2_eq hX, B_eq hX, fun _ hlt hRX => P1_max hX hlt hRX,
    fun _ hlt hRX => P2_max hX hlt hRX, B_le_normalizer⟩

open CFSG CFSG.ASVolI in
theorem facts7764 (hX : Nat.card ↥burnsideF48t_g23X = 4245696) : (∀ c ∈ burnsideF48t_g23K', c = 1 ∨ c = burnsideF48t_g23κ 0 ∨ c = burnsideF48t_g23κ 1 ∨
      c = burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) ∧
    (∀ x ∈ burnsideF48t_g23P1', x ∉ burnsideF48t_g23P2' →
      (∀ k ∈ burnsideF48t_g23K', x * k * x⁻¹ ∈ burnsideF48t_g23K') →
      (burnsideF48t_g23σ 2)⁻¹ * x ∈ burnsideF48t_g23K') ∧
    ∀ y ∈ burnsideF48t_g23P2', y ∉ burnsideF48t_g23P1' →
      (∀ k ∈ burnsideF48t_g23K', y * k * y⁻¹ ∈ burnsideF48t_g23K') →
      (burnsideF48t_g23σ 3)⁻¹ * y ∈ burnsideF48t_g23K' := by
  refine ⟨fun c hc => ?_, fun x hx hx2 hxK => ?_, fun y hy hy1 hyK => ?_⟩
  · rw [← kap_eq_kappa (j := 0) (by norm_num), ← kap_eq_kappa (j := 1) (by norm_num)]
    exact K_cases hc
  · rw [← sig_eq 2]
    exact xred hX hx hx2 hxK
  · rw [← sig_eq 3]
    exact yred hX hy hy1 hyK

end CFSG.KC.G23F48

end
