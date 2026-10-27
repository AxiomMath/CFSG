module

public import Certificates.Kernel.Sporadic.Fi24G2e.Bridge
public import Certificates.Kernel.Sporadic.Fi24Orb.Inj
public import Certificates.Kernel.Sporadic.Fi24G2e.OData
public import Certificates.Kernel.Sporadic.Fi24G2d.Final
public import CFSG.Certificates.Kernel.Spor.Fi24G2eSound
import Certificates.Kernel.Sporadic.Fi24G2e.OW
import Certificates.Kernel.Sporadic.Fi24G2e.CL
import Mathlib.Tactic.Group

public section

namespace CertificateChecks.KernelFi24G2e

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix CertificateChecks.KernelFi24Orb
  CertificateChecks.KernelFi24Ext CertificateChecks.KernelSpor.Fi24Rels TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KS.Mat3 CFSG.KD.Fi24G2e CFSG.KC.Fi24FixK CFSG.KC.Fi24FixS
  CFSG.KC.Fi24FixC

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24G2e.BX CFSG.KD.Fi24G2e.OX CFSG.KD.Fi24Ext.MX
  CFSG.KD.BrFi24.MT CFSG.KD.Fi24Fix.MX

noncomputable abbrev wp (w : List ℕ) : Fi24AutomorphismGroup := (w.map g0).prod

theorem wp_conj (q : List ℕ) : wp (q.reverse ++ 0 :: q) = (wp q)⁻¹ * g0 0 * wp q := by
  have h : ∀ w : List ℕ, wp w.reverse = (wp w)⁻¹ := by
    intro w
    induction w with
    | nil => simp [wp]
    | cons g w ih =>
      rw [List.reverse_cons]
      simp only [wp, List.map_append, List.prod_append] at ih ⊢
      rw [ih]
      simp [g0_inv]
  simp only [wp, List.map_append, List.prod_append, List.map_cons, List.prod_cons] at h ⊢
  rw [h, mul_assoc]

theorem ψ_conj {q : List ℕ} (hq : ∀ g ∈ q, g < 12) {r : ℕ} (hr : r < 306936) :
    ψ (walk CFSG.KD.Fi24Fix.TG (q.reverse ++ 0 :: q) r) = act (τ (wp q)⁻¹ * uT * τ (wp q)) (ψ r) := by
  have hw : ∀ g ∈ q.reverse ++ 0 :: q, g < 12 := by
    intro g hg
    simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact hq g hg
    · norm_num
    · exact hq g hg
  rw [ψ_walk_τ hw hr]
  change act (τ (wp (q.reverse ++ 0 :: q)))⁻¹ (ψ r) = _
  rw [wp_conj, map_mul, map_mul, map_inv, τ_g0_zero, mul_inv_rev, mul_inv_rev, inv_inv, uT_inv,
    mul_assoc]

theorem act_conj_own {q : List ℕ} (hq : ∀ g ∈ q, g < 12) :
    act (τ (wp q)⁻¹ * uT * τ (wp q)) (ψ (walk CFSG.KD.Fi24Fix.TG q 37886)) =
      ψ (walk CFSG.KD.Fi24Fix.TG q 37886) := by
  have h0 : CFSG.KD.Fi24Fix.TG 0 37886 = 37886 := by decide +kernel
  have hx := ψ_walk_τ hq (r := 37886) (by norm_num)
  have h1 : act uT (ψ 37886) = ψ 37886 := by
    rw [← τ_g0_zero, ← ψ_TG (by norm_num) (by norm_num), h0]
  rw [hx, ← act_mul]
  have e : τ (wp q)⁻¹ * uT * τ (wp q) * (τ (List.map g0 q).prod)⁻¹ = τ (wp q)⁻¹ * uT := by
    rw [mul_assoc (τ (wp q)⁻¹ * uT), show τ (wp q) * (τ (List.map g0 q).prod)⁻¹ = 1 from
      mul_inv_cancel _, mul_one]
  rw [e, act_mul, h1, map_inv]

theorem oq_lt : ∀ g ∈ OQ2 ++ OQ4 ++ OQ6, g < 12 := by decide +kernel

theorem letter_own :
    walk CFSG.KD.Fi24Fix.TG OQ2 37886 = 22978 ∧ walk CFSG.KD.Fi24Fix.TG OQ4 37886 = 22975 ∧
    walk CFSG.KD.Fi24Fix.TG OQ6 37886 = 22973 ∧
    τ (g0 2) = (τ (wp OQ2))⁻¹ * uT * τ (wp OQ2) ∧ τ (g0 4) = (τ (wp OQ4))⁻¹ * uT * τ (wp OQ4) ∧
    τ (g0 6) = (τ (wp OQ6))⁻¹ * uT * τ (wp OQ6) := by
  have key : ∀ (q : List ℕ) (Mq : ℕ) (g : ℕ), g < 12 → (∀ h ∈ q, h < 12) →
      Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG q CFSG.KD.BrFi24.ONE) Mq = true →
      Nat.beq (CFSG.KD.BrFi24.MUL (LG 0) Mq) (CFSG.KD.BrFi24.MUL Mq (LG g)) = true →
      τ (g0 g) = (τ (wp q))⁻¹ * uT * τ (wp q) := by
    intro q Mq g hg hq h1 h2
    have hw := wordMul_τ cn_one q hq
    rw [eq_of_beq h1, mt_one, Matrix.mul_one] at hw
    have e : uT * τ (wp q) = τ (wp q) * τ (g0 g) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, uT_val, ← hw.2, τ_g0 hg]
      rw [← (mul_mt (cn_LG (g := 0) (by norm_num)) hw.1).2, eq_of_beq h2,
        (mul_mt hw.1 (cn_LG hg)).2]
    rw [mul_assoc, e]
    group
  refine ⟨Nat.eq_of_beq_eq_true CFSG.KD.Fi24G2e.OW.p2, Nat.eq_of_beq_eq_true CFSG.KD.Fi24G2e.OW.p4,
    Nat.eq_of_beq_eq_true CFSG.KD.Fi24G2e.OW.p6, ?_, ?_, ?_⟩
  · exact key OQ2 MQ2 2 (by norm_num) (fun g hg => oq_lt g (by simp [hg]))
      CFSG.KD.Fi24G2e.OW.m2 CFSG.KD.Fi24G2e.OW.c2
  · exact key OQ4 MQ4 4 (by norm_num) (fun g hg => oq_lt g (by simp [hg]))
      CFSG.KD.Fi24G2e.OW.m4 CFSG.KD.Fi24G2e.OW.c4
  · exact key OQ6 MQ6 6 (by norm_num) (fun g hg => oq_lt g (by simp [hg]))
      CFSG.KD.Fi24G2e.OW.m6 CFSG.KD.Fi24G2e.OW.c6

theorem cq_lt : ∀ j < 696, ∀ g ∈ CQL j, g < 12 := by decide +kernel

theorem clause_F2D :
    (∀ j < 696, ∀ g ∈ CFSG.KD.Fi24G2d.W2D, act (τ (g0 g)) (ψ (CFSG.KD.Fi24G2d.F2D j)) =
      ψ (CFSG.KD.Fi24G2d.F2D j)) ∧
    ∀ j < 696, CFSG.KD.Fi24G2d.F2D j = 37886 ∨ CFSG.KD.Fi24G2d.F2D j = 22978 ∨
      CFSG.KD.Fi24G2d.F2D j = 22975 ∨
      (walk CFSG.KD.Fi24Fix.TG (CQL j) 37886 = CFSG.KD.Fi24G2d.F2D j ∧ CYF j < 696 ∧
        act (τ (wp (CQL j))⁻¹ * uT * τ (wp (CQL j))) (ψ (CFSG.KD.Fi24G2d.F2D (CYF j))) ≠
          ψ (CFSG.KD.Fi24G2d.F2D (CYF j))) := by
  have hF := CFSG.KD.Fi24G2d.F2D_spec
  refine ⟨fun j hj g hg => ?_, fun j hj => ?_⟩
  · have hfix : ∀ g' ∈ ([0, 2, 4] : List ℕ), CFSG.KD.Fi24Fix.TG g' (CFSG.KD.Fi24G2d.F2D j) =
        CFSG.KD.Fi24G2d.F2D j := by
      intro g' hg'
      have hl : CFSG.KC.Fi24G2d.fixLOK CFSG.KD.Fi24G2d.F2D CFSG.KD.Fi24Fix.TG [g'] 306936 696 = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl
        · exact CFSG.KD.Fi24G2e.CL.f0
        · exact CFSG.KD.Fi24G2e.CL.f2
        · exact CFSG.KD.Fi24G2e.CL.f4
      have := (CFSG.KC.Fi24G2dS.fixLOK_spec hl (by norm_num) j hj).2.1
      rwa [walk_cons, walk_nil] at this
    have hg12 : g < 12 := by
      simp only [CFSG.KD.Fi24G2d.W2D, List.mem_cons, List.not_mem_nil, or_false] at hg
      omega
    rw [← ψ_TG hg12 (hF j hj).1, hfix g hg]
  · rcases CFSG.KC.Fi24G2eS.clauseOK_spec CFSG.KD.Fi24G2e.CL.cl (by norm_num) j hj with
      h | h | h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨h1, h2, fun e => h3 ?_⟩))
      rw [← ψ_conj (cq_lt j hj) (hF _ h2).1] at e
      exact ψ_inj (walk_lt (by
        intro g hg
        simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hg
        rcases hg with hg | rfl | hg
        · exact cq_lt j hj g hg
        · norm_num
        · exact cq_lt j hj g hg) (hF _ h2).1) (hF _ h2).1 e

end CertificateChecks.KernelFi24G2e

end
