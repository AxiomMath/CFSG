module

public import Certificates.Data.Kernel.EvenSporM22.HS08Defs

public section

namespace CertificateChecks.KernelEvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.KC.EvenSporM22

set_option maxRecDepth 100000 in
theorem jOK_jLit : JOK jLit := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem outInvJ_jLit : OutInvPropJ jLit := by
  decide +kernel

end CertificateChecks.KernelEvenSporM22
