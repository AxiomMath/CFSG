module

public import Certificates.Data.Kernel.TwoM22.Check
public import Certificates.Data.Kernel.TwoM22.Data

public section

namespace CertificateChecks.TwoM22K

open CFSG.KC.TwoM22 CFSG.KD.TwoM22

theorem recs6 : recRange RT g660 g22 a b ai bi z11.1 z11.2 384 64 = true := by decide +kernel

end CertificateChecks.TwoM22K

end
