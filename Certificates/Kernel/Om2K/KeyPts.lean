module

public import Certificates.Data.Holder1711.Om2Check

public section

namespace CertificateChecks.KernelOm2

@[expose] def keyPtsYA : Array Nat :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check.keyPtsY.toArray

end CertificateChecks.KernelOm2

end
