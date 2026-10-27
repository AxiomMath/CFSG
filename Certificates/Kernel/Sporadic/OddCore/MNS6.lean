module

public import Certificates.Kernel.Sporadic.OddCore.MNSl
public import Certificates.Data.Kernel.Spor.MulHQ
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

#kc_slices CertificateChecks.KernelSpor.MNd.Q2aE CertificateChecks.KernelSpor.MNd.q2aE 4
#kc_slices CertificateChecks.KernelSpor.MNd.Q2aH CertificateChecks.KernelSpor.MNd.q2aH 1
#kc_slices CertificateChecks.KernelSpor.MNd.Q2bE CertificateChecks.KernelSpor.MNd.q2bE 2
#kc_slices CertificateChecks.KernelSpor.MNd.Q2bH CertificateChecks.KernelSpor.MNd.q2bH 1
#kc_slices CertificateChecks.KernelSpor.MNd.Q2cE CertificateChecks.KernelSpor.MNd.q2cE 2
#kc_slices CertificateChecks.KernelSpor.MNd.Q2cH CertificateChecks.KernelSpor.MNd.q2cH 1
#kc_slices CertificateChecks.KernelSpor.MNd.Q2dE CertificateChecks.KernelSpor.MNd.q2dE 1
#kc_slices CertificateChecks.KernelSpor.MNd.Q2dH CertificateChecks.KernelSpor.MNd.q2dH 1

namespace CertificateChecks.KernelSpor.MNd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem syCl : slK (Nat.mul MN.SY.cnt 6)
    (findPtK MN.SY.cnt MN.SY.T (prodQK 275 9 (mask 9) 6 MN.SY.T (bothK 3 (fun j => F (Nat.succ j))
      (fun j => I (Nat.succ j)))) MN.SYCl) 0 (Nat.mul MN.SY.cnt 6) = true := by quickRfl

theorem k_scov : allN MN.SY.cnt scovK = true := by quickRfl

end CertificateChecks.KernelSpor.MNd

end
