
module

public import Certificates.Kernel.M24L2.GlCheck
public import CFSG.Certificates.Kernel.M24L2.ReachSound

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2

@[expose] noncomputable def glL : List Nat := 33825 :: glES.flatten.map Prod.fst

theorem invK_all : ∀ k < 16, invChk glMask (Nat.mul 4096 k) 4096 = true := by
  intro k hk
  interval_cases k
  exacts [invK0, invK1, invK2, invK3, invK4, invK5, invK6, invK7, invK8, invK9, invK10, invK11,
    invK12, invK13, invK14, invK15]

theorem reach : ReachL glL ∧ glL.Nodup ∧ (∀ m ∈ glL, m < 65536) ∧ glL.length = 20160 := by
  obtain ⟨h1, h2, h3⟩ := reachL_of invK_all tree_ok
  refine ⟨h1, h2, h3, ?_⟩
  have h := Nat.eq_of_beq_eq_true glE_length
  unfold glL
  rw [List.length_cons, List.length_map, List.length_flatten, h]

end CertificateChecks.KernelM24L2
