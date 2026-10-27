module

public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueFacts
public import Certificates.Kernel.LyGlue.Facts4

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

noncomputable abbrev Hb : Subgroup (Perm (Fin Ly0.deg)) := closure (Glue.txyBp '' {l | l < 5})

theorem lineK_spec {T A : CV 1080} (h : lineK T.1 A.1 = true) :
    ev T * ev A = ev A * ev T ∨ ev T * ev A = (ev A)⁻¹ * ev T := by
  unfold lineK at h
  have e1 : eq22 1080 11 (mask 11) T.1 A.1 A.1 T.1 = eq22C T A A T := by
    unfold eq22C
    rw [wC1080]
  have e2 : eq22 1080 11 (mask 11) T.1 A.1 (pinvS 1080 11 (mask 11) A.1) T.1 = eq22C T A A⁻¹ T := by
    unfold eq22C
    rw [wC1080]
    rfl
  rw [e1, e2, eq22C_eq, eq22C_eq] at h
  cases h1 : decide (T * A = A * T)
  · rw [h1] at h
    have h2 : T * A = A⁻¹ * T := of_decide_eq_true h
    right
    rw [← ev_mul, ← ev_inv, ← ev_mul, h2]
  · left
    rw [← ev_mul, ← ev_mul, of_decide_eq_true h1]

theorem line_of_phi {Φ : ↥Ly0.UYperm ≃* ↥Ly1080.Y0} {x t : Perm (Fin Ly0.deg)}
    (hx : x ∈ Ly0.UYperm) (ht : t ∈ Ly0.UYperm)
    (h : (Φ ⟨t, ht⟩ : Perm (Fin 1080)) * Φ ⟨x, hx⟩ = (Φ ⟨x, hx⟩ : Perm (Fin 1080)) * Φ ⟨t, ht⟩ ∨
      (Φ ⟨t, ht⟩ : Perm (Fin 1080)) * Φ ⟨x, hx⟩ = (Φ ⟨x, hx⟩ : Perm (Fin 1080))⁻¹ * Φ ⟨t, ht⟩) :
    t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x⁻¹ := by
  rcases h with e | e
  · left
    have e' : Φ (⟨t, ht⟩ * ⟨x, hx⟩) = Φ (⟨x, hx⟩ * ⟨t, ht⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext e
    have := congrArg Subtype.val (Φ.injective e')
    change t * x = x * t at this
    rw [this]
    group
  · right
    have e' : Φ (⟨t, ht⟩ * ⟨x, hx⟩) = Φ (⟨x, hx⟩⁻¹ * ⟨t, ht⟩) := by
      rw [map_mul, map_mul, map_inv]
      exact Subtype.ext e
    have := congrArg Subtype.val (Φ.injective e')
    change t * x = x⁻¹ * t at this
    rw [this]
    group

theorem txyWords_getD {j : Nat} (hj : j < 5) :
    Ly1080.txyWords[j]! = Ly1080.txyWords.getD j [] := by
  interval_cases j <;> rfl

theorem xG_eq_word (hM : Ly0.ModelChecks) : Ly0.xG = Ly0.wG Ly0.gens0 Ly0.wordX :=
  Ly0.eq_of_rep (Ly0.rep_X hM.tab hM.struct) (by
    rw [← (Ly0.structCheck_spec hM.struct).2.2.2.2.2.1]
    exact Ly0.rep_word0 hM.tab _ fun l hl => Ly0.decodeWord_mem _ l hl)

theorem wordY_len : Ly0.wordY.length = 256 := by decide +kernel

theorem wordX_len : Ly0.wordX.length = 36 := by decide +kernel

end CertificateChecks.KernelLy

end
