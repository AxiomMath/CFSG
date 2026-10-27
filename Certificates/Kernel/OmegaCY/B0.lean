module

public import Certificates.Kernel.OmegaCY.Checks
public import Certificates.Kernel.A45Cls.Glue107
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls Subgroup

@[expose] def b0g (k : ℕ) : Equiv.Perm (Fin 45) := wvA (b0W.getD k [])

theorem prep_b0g : ∀ k < 4, PRep 45 6 (B0Z.G k) (b0g k) := by
  intro k hk
  have hl : b0W.length = 4 := rfl
  exact (prep_word cyBinds.1 (j := k) (by rw [hl]; exact hk)).1

theorem closure_comm {S : Set (Equiv.Perm (Fin 45))} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
  have h1 : closure S ≤ centralizer S :=
    closure_le _ |>.2 fun a ha => mem_centralizer_iff.2 fun b hb => hS b hb a ha
  intro x hx y hy
  have h2 : closure S ≤ centralizer {y} :=
    closure_le _ |>.2 fun a ha => mem_centralizer_iff.2 fun b hb => by
      rw [Set.mem_singleton_iff.1 hb]
      exact (mem_centralizer_iff.1 (h1 hy) a ha).symm
  exact (mem_centralizer_iff.1 (h2 hx) y rfl).symm

theorem b0_enum :
    ∃ c : ℕ → Equiv.Perm (Fin 45),
      (∀ i < 16, PRep 45 6 (B0Z.T i) (c i) ∧ c i ∈ CFSG.OddStandard.SmallF3.Omega.B0) ∧
      ∀ y ∈ CFSG.OddStandard.SmallF3.Omega.B0, ∃ i < 16, c i = y := by
  obtain ⟨c, hc, hall, hcard⟩ := enum_A prep_b0g B0Z.cl B0Z.tr (by norm_num) cyBinds.2 B0Z.k
  have hle : closure (b0g '' {k | k < 4}) ≤ T0 := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨c0, hc0, -⟩ := t0_enum
    obtain ⟨i, hi, e⟩ := inPts_spec (fun i hi => (hc0 i hi).1) (PK.allN_iff.1 cyB0.1 k hk)
      (prep_b0g k hk)
    rw [← e]
    exact (hc0 i hi).2
  have hcomm := closure_comm (S := b0g '' {k | k < 4}) (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact eq22_sound (PK.allN_iff.1 (PK.allN_iff.1 cyB0.2.2 a ha) b hb) (prep_b0g a ha)
      (prep_b0g b hb) (prep_b0g b hb) (prep_b0g a ha))
  have hB := CFSG.OddStandard.SmallF3.Omega.eq_B0_of_abelian hle hcomm (by rw [hcard]; rfl)
  rw [hB] at hc hall
  exact ⟨c, hc, hall⟩

end CertificateChecks.KernelA45

end
