module

public import Certificates.Kernel.Misc.GL4.A5Facts
public import Certificates.Kernel.Misc.GL4.KleinK
public import CFSG.Certificates.Kernel.Misc.GL4KleinSound

public section

namespace CertificateChecks.KernelMisc.GL4A5

open CFSG.KC.Misc.GL4 Certificates.A5GL42

theorem subLt : ∀ s ∈ subspaceCodes, ∀ x ∈ s, x < 16 := fun s hs => (subC.2.2.1 s hs).2

theorem kleinN : KleinN := by
  intro A hA
  rw [HN_eq] at hA ⊢
  obtain ⟨a, ha, b, hb, hk, rfl⟩ := klein_mem grpN.1 hA
  exact natFacts_of subspaces_complete subLt (kAc_lt (grpN.1 a ha) (grpN.1 b hb))
    (kleinNC a ha b hb hk)

theorem kleinO : KleinO := by
  intro A hA
  rw [HO_eq] at hA ⊢
  obtain ⟨a, ha, b, hb, hk, rfl⟩ := klein_mem grpO.1 hA
  exact orthFacts_of subspaces_complete subLt (kAc_lt (grpO.1 a ha) (grpO.1 b hb))
    (kleinOC a ha b hb hk)

end CertificateChecks.KernelMisc.GL4A5

end
