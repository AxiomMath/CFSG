module

public import Certificates.Kernel.LyY.Group

public section

namespace CertificateChecks.KernelLyY

open Equiv Subgroup CFSG.KS CFSG.KC.J2Enum CFSG.Sporadic.Recognition.LyonsSims.Ly1080
open CFSG.Certificates.ChainArrays (levT)

theorem card_Y0 : Nat.card Y0 = 349920 := by
  obtain ⟨hb, hh, hl, hNS, hs, -⟩ := chainYC
  obtain ⟨hmem, hsurj, hinj⟩ := GrpPf.enum3 hb hh hl hNS hs
  obtain ⟨-, -, e0, e1, e2, -⟩ := ties
  have hm : ∀ p : Fin 1080 × Fin 54 × Fin 6,
      levT 1080 yS yBase 0 p.1 * levT 1080 yS yBase 1 p.2.1 * levT 1080 yS yBase 2 p.2.2 ∈ GY :=
    fun p => mul_mem (mul_mem (hmem 0 (by norm_num) p.1 (by rw [e0]; exact p.1.2)).1
      (hmem 1 (by norm_num) p.2.1 (by rw [e1]; exact p.2.1.2)).1)
      (hmem 2 (by norm_num) p.2.2 (by rw [e2]; exact p.2.2.2)).1
  let f : Fin 1080 × Fin 54 × Fin 6 → ↥GY := fun p => ⟨_, hm p⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hinj p.1 (by rw [e0]; exact p.1.2) q.1 (by rw [e0]; exact q.1.2)
        p.2.1 (by rw [e1]; exact p.2.1.2) q.2.1 (by rw [e1]; exact q.2.1.2)
        p.2.2 (by rw [e2]; exact p.2.2.2) q.2.2 (by rw [e2]; exact q.2.2.2)
        (congrArg Subtype.val hpq)
      exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
    · obtain ⟨a, ha, b, hb', c, hc, hx⟩ := hsurj x x.2
      rw [e0] at ha
      rw [e1] at hb'
      rw [e2] at hc
      exact ⟨(⟨a, ha⟩, ⟨b, hb'⟩, ⟨c, hc⟩), Subtype.ext hx.symm⟩
  rw [Y0_eq, ← Nat.card_eq_of_bijective f hf]
  simp [Nat.card_prod]

end CertificateChecks.KernelLyY

end
