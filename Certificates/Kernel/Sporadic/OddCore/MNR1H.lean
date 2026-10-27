module

public import Certificates.Kernel.Sporadic.OddCore.MNSlF
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

#kc_slices CertificateChecks.KernelSpor.MNd.R1HF CertificateChecks.KernelSpor.MNd.r1HF 20

namespace CertificateChecks.KernelSpor.MNd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MulH

theorem ch2284hF_neg : hsortPtKF 275 9 (mask 9) MN.R1.cnt (fun _ => 0) MN.R1.HS MN.R1.HSI 0 =
    false := by
  decide +kernel

end CertificateChecks.KernelSpor.MNd

end
