
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Kernel.Ly3085.Seed

@[expose] public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Ly TauCeti

private theorem presentation_eq :
    SporadicName.Ly.presentation = Sporadic.Lyons.presentation := rfl

end CertificateChecks.KernelLy

end
