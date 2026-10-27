module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs

public section

namespace CertificateChecks.KernelU52F

open CFSG.ASVolI

@[expose] def u52eLA : Array (Array Nat) := burnsideF48t_u52eLArr ()

@[expose] def u52eLI : Array (Array Nat) := burnsideF48t_u52eLInv ()

end CertificateChecks.KernelU52F

end
