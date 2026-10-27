module

public import Certificates.Kernel.Sporadic.OddCore.McLTKHF
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Sporadic.OddCore.McLTK

public section

set_option maxRecDepth 400000

#kc_slices CertificateChecks.KernelSpor.McLTK.hSKF CertificateChecks.KernelSpor.McLTK.hSlF 28

namespace CertificateChecks.KernelSpor.McLTK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MulH

theorem ch6106hF_neg :
    hsortPtKF 275 9 (mask 9) McLTC.cnt (fun _ => 0) McLTC.HS McLTC.HSI 0 = false := by
  decide +kernel

end CertificateChecks.KernelSpor.McLTK

end
