module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Fi22.Final
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelFi22

theorem fi22 : Finite TauCeti.SporadicName.Fi22.Group ∧
    Nat.card TauCeti.SporadicName.Fi22.Group ≤ 64561751654400 :=
  fi22_bound

end CertificateChecks.KernelFi22

end
