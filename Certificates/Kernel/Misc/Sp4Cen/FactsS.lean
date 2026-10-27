module

public import Certificates.Kernel.Misc.Sp4Cen.Checks
public import CFSG.Certificates.Kernel.Misc.Sp4CenSound
import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CertificateChecks.KernelMisc.Sp4Cen

open Matrix CFSG.KD.Sp4Cen CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 CFSG.KC.Misc.Clos
  CFSG.KC.Misc.Sp4Cen
open Certificates.GL4 (GL4 sg)
open Certificates.A5GL42 (Mat4 ofCode)

@[expose] noncomputable def SB : Subgroup GL4 := sg [S0, S1]

theorem gens_inv : ∀ c ∈ [S0, S1], invOK c = true := by
  have h := andB_iff.1 sp4_gen_ok
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact h.1
  · exact h.2

theorem sb_exact : Nat.card SB = 720 ∧ ExactList enc4 SB 720 SBE := by
  have h := (CFSG.KC.LQT.P.allN_iff _ _).1 sp4_sb_ok
  refine sg_exact [S0, S1] gens_inv (G := SG2) (PA := SBP) (SG := SBS) (CT := SBC) ?_ (by norm_num)
    (fun k hk => (andB_iff.1 (h k hk)).1) (fun k hk => (andB_iff.1 (andB_iff.1 (h k hk)).2).1)
    (fun k hk => (andB_iff.1 (andB_iff.1 (h k hk)).2).2)
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j <;> rfl

@[expose] noncomputable def W0m : Mat4 := ofCode W0

@[expose] noncomputable def stabW : Subgroup GL4 where
  carrier := {g | (g : Mat4)ᵀ * W0m * (g : Mat4) = W0m}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul] at *
    calc (b : Mat4)ᵀ * (a : Mat4)ᵀ * W0m * ((a : Mat4) * b)
        = (b : Mat4)ᵀ * ((a : Mat4)ᵀ * W0m * a) * b := by simp only [Matrix.mul_assoc]
      _ = W0m := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : (a : Mat4) * ((a⁻¹ : GL4) : Mat4) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((a⁻¹ : GL4) : Mat4)ᵀ * W0m * ((a⁻¹ : GL4) : Mat4)
        = ((a⁻¹ : GL4) : Mat4)ᵀ * ((a : Mat4)ᵀ * W0m * a) * ((a⁻¹ : GL4) : Mat4) := by rw [ha]
      _ = ((a : Mat4) * ((a⁻¹ : GL4) : Mat4))ᵀ * W0m * ((a : Mat4) * ((a⁻¹ : GL4) : Mat4)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = W0m := by
          rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem fix0 : Nat.beq (formF W0 S0) W0 = true := by quickRfl

theorem fix1 : Nat.beq (formF W0 S1) W0 = true := by quickRfl

theorem mem_stabW_of_enc {g : GL4} {c : ℕ} (e : enc4 g = c) (h : formF W0 c = W0) : g ∈ stabW := by
  change (g : Mat4)ᵀ * W0m * (g : Mat4) = W0m
  rw [W0m, ← ofCode_formF_enc, e, h]

theorem sb_le_stab : SB ≤ stabW := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  have hl : ∀ c ∈ [S0, S1], c < 65536 := fun c hc => by
    obtain ⟨u, hu⟩ := exists_of_invOK (gens_inv c hc)
    rw [← hu]
    exact code4_lt _
  have hm := (mem_pset_iff hl).1 hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e
  · exact mem_stabW_of_enc e (Nat.eq_of_beq_eq_true fix0)
  · exact mem_stabW_of_enc e (Nat.eq_of_beq_eq_true fix1)

theorem card_GL4 : Nat.card GL4 = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_succ]

theorem formAt_parts {k : ℕ} (hk : k < 28) : invW (f16 (FG k) 0) (f16 (FG k) 1) = true ∧
    formF W0 (f16 (FG k) 0) = FM k ∧ ∀ j < 28, FM j = FM k → j = k := by
  have h := (CFSG.KC.LQT.P.allN_iff _ _).1 (andB_iff.1 sp4_form_ok).2 k hk
  rw [formAt, CFSG.KC.LQT.P.letB_eq, andB_iff, andB_iff, andB_iff] at h
  refine ⟨h.1.1, Nat.eq_of_beq_eq_true h.1.2, fun j hj e => ?_⟩
  have hd := (CFSG.KC.LQT.P.allN_iff _ _).1 h.2.1 j hj
  exact Nat.eq_of_beq_eq_true (impB_iff.1 hd (by rw [e]; exact Nat.beq_refl _))

theorem fm_lt {k : ℕ} (hk : k < 28) : FM k < 65536 := by
  rw [← (formAt_parts hk).2.1]
  exact mul4F_lt _ _

theorem form_spec : (∀ k < 28, ∃ g : GL4, (g : Mat4)ᵀ * W0m * (g : Mat4) = ofCode (FM k)) ∧
    ∀ i < 28, ∀ j < 28, FM i = FM j → i = j := by
  refine ⟨fun k hk => ?_, fun i hi j hj e => (formAt_parts hj).2.2 i hi e⟩
  obtain ⟨u, hu, -⟩ := invW_sound (f16_lt _ _) (f16_lt _ _) (formAt_parts hk).1
  refine ⟨u, ?_⟩
  rw [W0m, ← ofCode_formF_enc, hu, (formAt_parts hk).2.1]

theorem sb_eq_stab : SB = stabW := by
  classical
  have hfs := form_spec
  choose! u hu using hfs.1
  have hinj : ∀ i < 28, ∀ j < 28,
      (QuotientGroup.mk (u i)⁻¹ : GL4 ⧸ stabW) = QuotientGroup.mk (u j)⁻¹ → i = j := by
    intro i hi j hj e
    rw [QuotientGroup.eq, inv_inv] at e
    change ((u i * (u j)⁻¹ : GL4) : Mat4)ᵀ * W0m * ((u i * (u j)⁻¹ : GL4) : Mat4) = W0m at e
    have hv : ((u i : GL4) : Mat4) = ((u i * (u j)⁻¹ : GL4) : Mat4) * (u j : Mat4) := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    have hf : ofCode (FM i) = ofCode (FM j) := by
      rw [← hu i hi, ← hu j hj, hv, Matrix.transpose_mul]
      calc ((u j : GL4) : Mat4)ᵀ * ((u i * (u j)⁻¹ : GL4) : Mat4)ᵀ * W0m *
            (((u i * (u j)⁻¹ : GL4) : Mat4) * (u j : Mat4))
          = ((u j : GL4) : Mat4)ᵀ * (((u i * (u j)⁻¹ : GL4) : Mat4)ᵀ * W0m *
            ((u i * (u j)⁻¹ : GL4) : Mat4)) * (u j : Mat4) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [e]
    exact hfs.2 i hi j hj (ofCode_inj (fm_lt hi) (fm_lt hj) hf)
  have h28 : 28 ≤ stabW.index := by
    rw [Subgroup.index]
    have : Function.Injective fun k : Fin 28 => (QuotientGroup.mk (u k)⁻¹ : GL4 ⧸ stabW) := fun a b e =>
      Fin.ext (hinj a a.2 b b.2 e)
    simpa using Nat.card_le_card_of_injective _ this
  have hcard : Nat.card stabW * stabW.index = 20160 := by
    rw [Subgroup.card_mul_index, card_GL4]
  have hle : Nat.card stabW ≤ 720 := by
    by_contra hc
    have : 721 * 28 ≤ Nat.card stabW * stabW.index := Nat.mul_le_mul (Nat.lt_of_not_le hc) h28
    omega
  exact Subgroup.eq_of_le_of_card_ge sb_le_stab (by rw [sb_exact.1]; exact hle)

end CertificateChecks.KernelMisc.Sp4Cen

end
