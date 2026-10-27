module

public import Certificates.Data.HuppertU38Three.Data

public section

namespace CertificateChecks.KernelU38Three

open U38Three

@[expose] def pGens : Array (Array Nat) := #[pa, pb]

@[expose] def lGens : Array (Array Nat) := #[la, lb]

@[expose] def pBase : Array Nat := #[0, 1, 2]

end CertificateChecks.KernelU38Three

end
