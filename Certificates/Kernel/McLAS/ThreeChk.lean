module

public import Certificates.Kernel.McLAS.ThreeRec
public import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 400000

#kc_slice_range CertificateChecks.KernelMcLAS.cmSl CertificateChecks.KernelMcLAS.ThreeChk.ca 0 154
#kc_slice_range CertificateChecks.KernelMcLAS.tcSl CertificateChecks.KernelMcLAS.ThreeChk.ct 0 4
#kc_slice_range CertificateChecks.KernelMcLAS.bSl CertificateChecks.KernelMcLAS.ThreeChk.cb 0 3
#kc_slice_range CertificateChecks.KernelMcLAS.rlSl CertificateChecks.KernelMcLAS.ThreeChk.cr 0 5

namespace CertificateChecks.KernelMcLAS.ThreeChk

#kc_forall_tree cm_all (fun s => CertificateChecks.KernelMcLAS.cmSl s = true) 154
  CertificateChecks.KernelMcLAS.ThreeChk.ca
#kc_forall_tree tc_all (fun s => CertificateChecks.KernelMcLAS.tcSl s = true) 4
  CertificateChecks.KernelMcLAS.ThreeChk.ct
#kc_forall_tree b_all (fun s => CertificateChecks.KernelMcLAS.bSl s = true) 3
  CertificateChecks.KernelMcLAS.ThreeChk.cb
#kc_forall_tree rl_all (fun s => CertificateChecks.KernelMcLAS.rlSl s = true) 5
  CertificateChecks.KernelMcLAS.ThreeChk.cr

theorem x_in_t : CFSG.KS.McLAS.atK CertificateChecks.KernelSpor.McLTT.cnt
    CertificateChecks.KernelSpor.McLTT.T CertificateChecks.KernelMcLAS.XinT (nat_lit 0)
    (CertificateChecks.KernelMcLAS.TT.F (nat_lit 0)) = true := by quickRfl

end CertificateChecks.KernelMcLAS.ThreeChk

end
