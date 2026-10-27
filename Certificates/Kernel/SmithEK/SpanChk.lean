module

public import Certificates.Data.Kernel.SmithEKS
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.Tab

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem spanW_ok : pts.L.all (fun p => spanOKL (tvW cT.L p)) = true := by
  decide +kernel

theorem spanW_neg_id : spanOKL ((List.range 20).map (2 ^ ·)) = false := by
  decide +kernel

theorem spanW_neg_col : spanOKL ((tvW cT.L (pts.L.getD 0 0)).set 3 0) = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
