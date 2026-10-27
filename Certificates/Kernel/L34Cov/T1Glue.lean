
module

public import Certificates.Kernel.L34Cov.T1Checks
public import Certificates.Kernel.L34Cov.WordsGlue
public import Certificates.Kernel.L34Cov.Glue
public import Certificates.Kernel.L34W.Glue
public import CFSG.Certificates.Kernel.L34Cov.T1Sound
public import CFSG.Certificates.Kernel.L34Cov.AlphaOKSound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.Multipliers.MonoAllR

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable Subgroup
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CertificateChecks.KernelL34W

#kc_forall_tree ch22219t1c_all (fun k => t1colsOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab T1X.F
  TwC.codes k = true) 64 CertificateChecks.KernelL34Cov.ch22219t1c.c

#kc_forall_tree ch22219t1a_all (fun k => Mono.allR 0 64 (t1clsOK T1X.F k) = true) 64
  CertificateChecks.KernelL34Cov.ch22219t1a.a

theorem tw_codes (k : ℕ) : (tw k).map letterCode = TwC.codes.getD k [] := by
  rw [(tw_eq k).1]
  exact map_letterCode_decL (tw_eq k).2

theorem zw_eq_zHom (a b c : ℕ) :
    z₁ ^ a * z₂ ^ b * z₃ ^ c = zHom (Multiplicative.ofAdd (a : ZMod 4),
      Multiplicative.ofAdd (b : ZMod 4), Multiplicative.ofAdd (c : ZMod 3)) := by
  rw [zHom_apply, mul_assoc]
  simp only [toAdd_ofAdd, ZMod.val_natCast]
  rw [← pow_eq_pow_mod a z₁_pow, ← pow_eq_pow_mod b z₂_pow, ← pow_eq_pow_mod c z₃_pow]

theorem zw_mem_center (a b c : ℕ) :
    z₁ ^ a * z₂ ^ b * z₃ ^ c ∈ center Cover :=
  mul_mem (mul_mem (pow_mem z₁_mem_center _) (pow_mem z₂_mem_center _)) (pow_mem z₃_mem_center _)

theorem zw_mul_eq {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ : ℕ}
    (h₁ : (a₁ + b₁) % 4 = (c₁ + d₁) % 4) (h₂ : (a₂ + b₂) % 4 = (c₂ + d₂) % 4)
    (h₃ : (a₃ + b₃) % 3 = (c₃ + d₃) % 3) :
    z₁ ^ a₁ * z₂ ^ a₂ * z₃ ^ a₃ * (z₁ ^ b₁ * z₂ ^ b₂ * z₃ ^ b₃) =
      z₁ ^ c₁ * z₂ ^ c₂ * z₃ ^ c₃ * (z₁ ^ d₁ * z₂ ^ d₂ * z₃ ^ d₃) := by
  rw [zw_eq_zHom, zw_eq_zHom, zw_eq_zHom, zw_eq_zHom, ← map_mul, ← map_mul]
  congr 1
  simp only [Prod.mk_mul_mk, ← ofAdd_add, ← Nat.cast_add, Prod.mk.injEq,
    EmbeddingLike.apply_eq_iff_eq]
  exact ⟨(ZMod.natCast_eq_natCast_iff' _ _ _).2 h₁, (ZMod.natCast_eq_natCast_iff' _ _ _).2 h₂,
    (ZMod.natCast_eq_natCast_iff' _ _ _).2 h₃⟩

theorem t1_quad {k l : ℕ} (hk : k < 64) (hl : l < 64) :
    t1Entry k l = (ent T1X.F k l / 48, ent T1X.F k l % 48 / 12, ent T1X.F k l % 12 / 3,
      ent T1X.F k l % 3) :=
  t1Of k l hk hl

theorem t1_lt' {k l : ℕ} (hk : k < 64) (hl : l < 64) : ent T1X.F k l / 48 < 64 := by
  have := bounds_T bounds_k hk hl
  omega

theorem cv_zOf (e : ℕ × ℕ × ℕ × ℕ) :
    cv (zOf e) = z₁ ^ e.2.1 * z₂ ^ e.2.2.1 * z₃ ^ e.2.2.2 := cv_zword _ _ _

theorem gens_lt : ∀ g ∈ [1, 2, 16, 20], g < 64 := by decide

theorem t1_spec_k :
    ∀ k < 64, ∀ l < 64, (t1Entry k l).1 < 64 ∧
      cv (tw k) * cv (tw l) = cv (tw (t1Entry k l).1) * cv (zOf (t1Entry k l)) := by
  have hm : ∀ k < 64, ∀ l < 64, (t1Entry k l).1 < 64 := fun k hk l hl => by
    rw [t1_quad hk hl]
    exact t1_lt' hk hl
  have hmain := mul_spec_of_gens (fun k => cv (tw k)) (fun k l => (t1Entry k l).1)
    (fun k l => cv (zOf (t1Entry k l))) [1, 2, 16, 20]
    (fun a b => by rw [cv_zOf]; exact zw_mem_center _ _ _)
    (by rw [(tw_eq 0).1]; rfl) hm
    (fun k hk => by
      have h0 := CFSG.Certificates.Mono.allR_spec t1zero_k k (Nat.zero_le _) hk
      have e : ent T1X.F k 0 = 48 * k := Nat.eq_of_beq_eq_true h0
      rw [t1_quad hk (by norm_num), e]
      refine ⟨by omega, ?_⟩
      rw [cv_zOf]
      have e1 : 48 * k % 48 / 12 = 0 := by omega
      have e2 : 48 * k % 12 / 3 = 0 := by omega
      have e3 : 48 * k % 3 = 0 := by omega
      simp only [e1, e2, e3, pow_zero, mul_one])
    (fun k hk g hg => by
      have hc := ch22219t1c_all k hk
      unfold t1colsOK at hc
      simp only [andB_eq, Bool.and_eq_true] at hc
      have hg' : t1colOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab T1X.F TwC.codes k g = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact hc.1
        · exact hc.2.1
        · exact hc.2.2.1
        · exact hc.2.2.2
      have hg64 := gens_lt g hg
      unfold t1colOK at hg'
      rw [bindB_eq, ← tw_codes, ← tw_codes, ← tw_codes, ← map_letterCode_invRev,
        ← List.map_append, ← List.map_append] at hg'
      have hid : cv (tw k ++ tw g ++ FreeGroup.invRev (tw (ent T1X.F k g / 48))) =
          z₁ ^ (ent T1X.F k g % 48 / 12) * z₂ ^ (ent T1X.F k g % 12 / 3) * z₃ ^ (ent T1X.F k g % 3) :=
        cv_eq_of_cvIdOK vt_k modelA modelB hg'
      rw [cv_append, cv_append, cv_invRev] at hid
      rw [t1_quad hk hg64, cv_zOf]
      try dsimp only
      rw [← hid]
      have hcen := zw_mem_center (ent T1X.F k g % 48 / 12) (ent T1X.F k g % 12 / 3)
        (ent T1X.F k g % 3)
      rw [← hid] at hcen
      have := mem_center_iff.1 hcen (cv (tw (ent T1X.F k g / 48)))
      calc cv (tw k) * cv (tw g) = cv (tw k) * cv (tw g) * (cv (tw (ent T1X.F k g / 48)))⁻¹ *
          cv (tw (ent T1X.F k g / 48)) := by group
        _ = _ := by rw [← this])
    (fun k hk l hl g hg => by
      have hg64 := gens_lt g hg
      have ha := CFSG.Certificates.Mono.allR_spec (ch22219t1a_all k hk) l (Nat.zero_le _) hl
      unfold t1clsOK at ha
      simp only [andB_eq, Bool.and_eq_true] at ha
      have hg' : t1clOK T1X.F k l g = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact ha.1
        · exact ha.2.1
        · exact ha.2.2.1
        · exact ha.2.2.2
      unfold t1clOK at hg'
      simp only [bindB_eq, andB_eq, Bool.and_eq_true] at hg'
      obtain ⟨hidx, hz⟩ := hg'
      unfold zEqOK at hz
      simp only [andB_eq, Bool.and_eq_true] at hz
      obtain ⟨z1, z2, z3⟩ := hz
      have hkl := t1_lt' hk hl
      have hlg := t1_lt' hl hg64
      rw [t1_quad hk hl, t1_quad hl hg64]
      try dsimp only
      rw [t1_quad hkl hg64, t1_quad hk hlg]
      try dsimp only
      refine ⟨Nat.eq_of_beq_eq_true hidx, ?_⟩
      rw [cv_zOf, cv_zOf, cv_zOf, cv_zOf]
      exact zw_mul_eq (Nat.eq_of_beq_eq_true z1) (Nat.eq_of_beq_eq_true z2)
        (Nat.eq_of_beq_eq_true z3))
    (fun S h0 hstep => reach_all reach_k S h0 fun l hl hS g hg => by
      have := hstep l hl hS g hg
      rw [t1_quad hl (gens_lt g hg)] at this
      exact this)
  exact fun k hk l hl => ⟨hm k hk l hl, hmain k hk l hl⟩

end CertificateChecks.KernelL34Cov

end
