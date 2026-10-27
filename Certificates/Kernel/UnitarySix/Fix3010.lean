
module

public import Certificates.Kernel.UnitarySix.Fix3010Base

public import Certificates.Kernel.UnitarySix.Struct3010
public import Certificates.Kernel.UnitarySix.Fischer
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

open scoped Pointwise in
theorem fix3010 :
    {p : Fin 693 | j3 p = p} = CFSG.Certificates.finSet 693 fixA ∧
      (∀ a ∈ aGens, ∀ p ∈ CFSG.Certificates.finSet 693 fixA, a p = p) ∧
      891 ≤ (Set.range fun g : Subgroup.closure {g | g ∈ u62Letters} =>
        g • CFSG.Certificates.finSet 693 fixA).ncard :=
  sound3010F letters_eq aWN_eq fixA_lt (by decide) (by decide) k3010F

end CertificateChecks.KernelU6

end
