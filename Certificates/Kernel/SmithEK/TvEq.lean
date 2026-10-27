module

public import Certificates.Kernel.SmithEK.Pts
public import CFSG.Certificates.Kernel.SmithEK.TvSound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem tvCols_eq (k : Nat) : tvCols k = (tvK (pts.L.getD k 0)).toArray :=
  tvCols_eq_of uPts_eq k

end CertificateChecks.KernelSmithEK
