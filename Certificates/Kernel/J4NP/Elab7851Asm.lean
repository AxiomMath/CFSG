module

public import CFSG.Certificates.Kernel.J4NP.Elab7851Sound
public import Certificates.Kernel.J4NP.Elab7851ChkRow
public import Certificates.Kernel.J4NP.Elab7851ChkEnt
public import Certificates.Kernel.J4Q.MaskU

public section

namespace CertificateChecks.KernelJ4NP

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.KC.J4NP CFSG.KD.J4NP

theorem chk7851 : Chk7851 CFSG.KD.J4Q.mkTL KK CMK PRK FMK XP MK FL ENT :=
  ⟨ch7851_pin, ch7851_xp, ch7851_root, CFSG.KD.J4NP.ch7851R.all, CFSG.KD.J4NP.ch7851E.all⟩

theorem star7851 :
    ∀ A : Subgroup J, A ≤ P0 → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) →
      ¬ A ≤ Eg uJ 11 → Nat.card ↥A ≤ 2 ^ 10 :=
  star_of_chk CertificateChecks.KernelJ4Q.tabL_eq chk7851

end CertificateChecks.KernelJ4NP

end
