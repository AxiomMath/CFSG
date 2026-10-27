
module

public import Certificates.Kernel.J4Count.FixZBase

public import CFSG.Sporadic.Schreier.J4SNoCompCoverBase1

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.KC.J4Count CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4NoCK CertificateChecks.KernelSporSch.J4NoCP

section Rep

end Rep

section Class

end Class

theorem orbit_H_subset {l : ℕ} (hl : l < 7) {x : Row}
    (hx : x ∈ orbit H (qv l)) : x ∈ orbit J v := by
  obtain ⟨h, rfl⟩ := hx
  refine ⟨(h : J) * (mRep l)⁻¹, ?_⟩
  change ((h : J) * (mRep l)⁻¹) • v = (h : J) • qv l
  rw [mul_smul, mRep_inv_smul_v hl]

end CertificateChecks.KernelJ4Count

end
