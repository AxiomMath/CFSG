module

public import Certificates.Kernel.Misc.Perm.Sp4ReachChecks
public import CFSG.Quasithin.Background.Sp4InfA6GenInputs
public import CFSG.Quasithin.Background.Sp4InfA6BasicInputs
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.Misc.PermDepthSound
import CFSG.Certificates.Kernel.Misc.PermClosProof
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop
import CFSG.Quasithin.Background.Sp4InfA6BasicBase

public section

namespace CertificateChecks.KernelMisc.Sp4Reach

open Equiv CFSG.KC.Misc.Clos CFSG.KC.LQT CFSG.Quasithin.Sp4Inf
open scoped Pointwise

theorem sign_gu : Perm.sign gu = 1 := by
  unfold gu
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  simp

theorem sign_gv : Perm.sign gv = 1 := by
  unfold gv
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_mul, Perm.sign_swap (by decide),
    Perm.sign_swap (by decide), Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  simp

theorem gu_mem : gu ∈ q1 := by
  rw [mem_q1, bq1, decide_eq_true_eq]
  exact ⟨by decide +kernel, sign_gu⟩

theorem gv_mem : gv ∈ q2 := by
  rw [mem_q2, bq2, decide_eq_true_eq]
  exact ⟨by decide +kernel, sign_gv⟩

theorem hG : ∀ j < [gu, gv].length, G j = pcode ([gu, gv].getD j 1) := by decide +kernel

theorem reach_succ (u v : Perm (Fin 6)) (d : ℕ) :
    reach u v (d + 1) = reachStep u v (reach u v d) := by
  unfold reach
  rw [Function.iterate_succ_apply']

theorem reach_mono (u v : Perm (Fin 6)) : Monotone (reach u v) := by
  refine monotone_nat_of_le_succ fun d => Finset.le_iff_subset.2 fun x hx => ?_
  rw [reach_succ]
  unfold reachStep
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem reach_step (d : ℕ) (g : Perm (Fin 6)) (l : ℕ) (hl : l < [gu, gv].length)
    (hg : g ∈ reach gu gv d ∧ Perm.sign g = 1) :
    g * [gu, gv].getD l 1 ∈ reach gu gv (d + 1) ∧ Perm.sign (g * [gu, gv].getD l 1) = 1 := by
  rw [reach_succ]
  unfold reachStep
  have hl2 : l = 0 ∨ l = 1 := by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  rcases hl2 with rfl | rfl
  · refine ⟨Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (· * gu) hg.1)), ?_⟩
    change Perm.sign (g * gu) = 1
    rw [Perm.sign_mul, hg.2, sign_gu, one_mul]
  · refine ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem (· * gv) hg.1), ?_⟩
    change Perm.sign (g * gv) = 1
    rw [Perm.sign_mul, hg.2, sign_gv, one_mul]

theorem card_alt : (Finset.univ.filter fun x : Perm (Fin 6) => Perm.sign x = 1).card = 360 := by
  have h2 := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at h2
  have h3 : Fintype.card (alternatingGroup (Fin 6)) =
      (Finset.univ.filter fun x : Perm (Fin 6) => Perm.sign x = 1).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by
      simp [Equiv.Perm.mem_alternatingGroup])
  have h6 : Nat.factorial 6 = 720 := by decide
  omega

theorem alt_subset_reach :
    (Finset.univ.filter (fun x : Perm (Fin 6) => Perm.sign x = 1)) ⊆ reach gu gv 14 := by
  classical
  have henc := pcode_enc_proved (n := 6) (by norm_num)
  have hr := reach_of_tree henc [gu, gv] hG ((CFSG.KC.Misc.Clos.allN_iff _ _).1 treeB)
    ((CFSG.KC.Misc.Clos.allN_iff _ _).1 depthB)
    (fun d g => g ∈ reach gu gv d ∧ Perm.sign g = 1)
    ⟨by unfold reach; simp, Perm.sign_one⟩ reach_step
  choose! f hfe hfR using hr
  have hdist := sort_distinct ((CFSG.KC.Misc.Clos.allN_iff _ _).1 sortB)
  have hdep := (CFSG.KC.Misc.Clos.allN_iff _ _).1 depthB
  let F : Fin 360 → Perm (Fin 6) := fun k => f k
  have hF : Function.Injective F := fun a b hab => Fin.ext (hdist a a.isLt b b.isLt (by
    rw [← hfe a a.isLt, ← hfe b b.isLt]
    exact congrArg pcode hab))
  have hsub : Finset.univ.image F ⊆
      Finset.univ.filter fun x : Perm (Fin 6) => Perm.sign x = 1 := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hfR k k.isLt).2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [card_alt, Finset.card_image_of_injective _ hF, Finset.card_univ, Fintype.card_fin])
  intro x hx
  rw [← heq] at hx
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.le_iff_subset.1 (reach_mono gu gv (depth_le (hdep k k.isLt))) (hfR k k.isLt).1

end CertificateChecks.KernelMisc.Sp4Reach

end
