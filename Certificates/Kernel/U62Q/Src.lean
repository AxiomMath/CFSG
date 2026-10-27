module

public import Certificates.Data.U62Rank.Check

public section

namespace CertificateChecks.KernelU62Q

@[expose] def u62Gs : Array (Array Nat) := U62Rank.sylowGens ()

end CertificateChecks.KernelU62Q

end
