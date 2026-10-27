module

public import CFSG.Certificates.Kernel.Fi22Gen.Sound
public import Certificates.Kernel.Fi22Gen.Checks
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenInputs
import Certificates.Kernel.Fi22Core.OrbData

public section

namespace CertificateChecks.KernelFi22Gen

open CFSG.KS.Fi22Gen CFSG.KD.Fi22Gen CFSG.Sporadic.Fi22 CFSG.Sporadic.Th CFSG.Perm
  CFSG.Sporadic.Fi22.Native
open scoped Pointwise

@[expose] def Uset : Finset (Fin 3510) :=
  Finset.univ.filter fun x => x.val ∈ CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted

theorem UL_eq : UL = CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted := by decide

theorem N_eq : N = 891 := by decide

theorem mem_Uset (y : Fin 3510) : y ∈ Uset ↔ ∃ j < 22, gD UL j = y.val := by
  rw [Uset, Finset.mem_filter, ← UL_eq]
  simp only [Finset.mem_univ, true_and]
  exact mem_iff_gD (by rw [UL_eq]; decide) _


theorem letters_act : ∀ l < 32, ∀ x (hx : x < 3510),
    (pairG gs l • (⟨x, hx⟩ : Fin 3510)).val = LT l x := by
  intro l hl x hx
  have h1 := rep_pairG_all l (by rw [chainLetters_size, chainWords_size]; omega) x hx
  unfold CFSG.Sporadic.Fi22.orb at h1
  rw [CertificateChecks.KernelFi22C.orbitData_eq, idx_of_lt _ hx] at h1
  rw [← h1]
  exact ((CertificateChecks.KernelFi22C.letters_TR hl).2 x hx).1

@[expose] noncomputable def gab (c : Nat) : J := if c = 0 then a else b

theorem gen_act : ∀ c < 2, ∀ x (hx : x < 3510), (gab c • (⟨x, hx⟩ : Fin 3510)).val = AB c x := by
  intro c hc x hx
  have hA := rep_alpha x hx
  have hB := rep_beta x hx
  unfold CFSG.Sporadic.Fi22.orb at hA hB
  rw [CertificateChecks.KernelFi22C.orbitData_eq, idx_of_lt _ hx] at hA hB
  interval_cases c
  · rw [gab, if_pos rfl, ← hA]
    exact (CertificateChecks.KernelFi22C.alpha_get hx).1
  · rw [gab, if_neg (by decide), ← hB]
    exact (CertificateChecks.KernelFi22C.beta_get hx).1

theorem sep5 (g : J) (h : ∀ i < 5, ∀ hi : BS i < 3510, g • (⟨BS i, hi⟩ : Fin 3510) = ⟨BS i, hi⟩) :
    g = 1 := by
  have hl : ∀ i ≤ 5, g ∈ lvl i := by
    intro i hi
    induction i with
    | zero => exact mem_lvl_zero g
    | succ i ih =>
      refine (chain_facts'.2.1 i (by rw [chainBase_size]; omega) g (ih (by omega))).1 ?_
      have hi5 : i < 5 := by omega
      have hb : chainBase[i]! = BS i := by interval_cases i <;> decide
      have hlt : BS i < 3510 := by interval_cases i <;> decide
      rw [hb, idx_of_lt g hlt, h i hi5 hlt]
  have hc := chain_facts'.2.2 5 (by rw [chainBase_size])
  rw [chainBase_size, Finset.Ico_self, Finset.prod_empty] at hc
  have hb := Subgroup.eq_bot_of_card_eq _ hc
  have hg := hl 5 le_rfl
  rw [hb] at hg
  exact (Subgroup.mem_bot).1 hg

theorem orbit_U_ge : 142155 ≤ Nat.card (MulAction.orbit J Uset) := by
  have h := orbit_ge_of_treeK fg_tree_ok (pairG gs) letters_act Uset mem_Uset
  rw [N_eq] at h
  omega

theorem orbit_t0_ge : 443520 ≤ Nat.card (MulAction.orbit
    (Subgroup.closure {x : J | x • Uset = Uset ∧ Odd (orderOf x)})
    (![190, 195, 526, 594, 752] : Fin 5 → Fin 3510)) := by
  have hul := (treeK_spec fg_tree_ok).1
  obtain ⟨o1, o2, s1, s2⟩ := elts_of_checks hul fg_ord_ok fg_trace_ok gab gen_act sep5 Uset
    mem_Uset
  have h1 : wG gab w1 ∈ Subgroup.closure {x : J | x • Uset = Uset ∧ Odd (orderOf x)} :=
    Subgroup.subset_closure ⟨s1, Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one o1)⟩
  have h2 : wG gab w2 ^ 2 ∈ Subgroup.closure {x : J | x • Uset = Uset ∧ Odd (orderOf x)} :=
    Subgroup.subset_closure ⟨s2, Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one o2)⟩
  have h := orbit_ge_of_chainK hul fg_ord_ok fg_trace_ok fg_chain_ok gab gen_act _ h1 h2
  have ht : (fun j : Fin 5 => tP UL j) = ![190, 195, 526, 594, 752] := by
    funext j
    fin_cases j <;> decide
  rwa [ht] at h

end CertificateChecks.KernelFi22Gen

end
