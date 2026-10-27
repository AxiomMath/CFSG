module

public import Certificates.Data.Kernel.SmithEKC
public import Certificates.Data.SMod20BasicData
public import Certificates.Kernel.SmithEK.TPack
public import Certificates.Kernel.SmithEK.WData
public import Certificates.Kernel.UnitarySix.Tables

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem c21260pt_len : ptWords.toList.length = 693 := by decide +kernel

theorem c21260pair_len : pairWords.toList.length = 693 := by decide +kernel

theorem c21260plane_len : planeWords.toList.length = 891 := by decide +kernel

theorem c21260pt : ptWK CertificateChecks.KernelU6.T.R ptWords.toList 0 = true := by
  decide +kernel

theorem c21260pair : pairWK CertificateChecks.KernelU6.T.R (pts.L.getD 0 0) pairWords.toList
    pts.L 0 = true := by
  decide +kernel

theorem c21260plane : planeWK tp.C (wd.W.getD 0 0) planeWords.toList wd.W = true := by
  decide +kernel

theorem c21260neg_pt : ptWK CertificateChecks.KernelU6.T.R
    (ptWords.toList.set 1 (ptWords.toList.getD 2 [])) 0 = false := by
  decide +kernel

theorem c21260neg_pair : pairWK CertificateChecks.KernelU6.T.R (pts.L.getD 0 0)
    (pairWords.toList.set 3 (pairWords.toList.getD 4 [])) pts.L 0 = false := by
  decide +kernel

theorem c21260neg_plane : planeWK tp.C (wd.W.getD 0 0)
    (planeWords.toList.set 1 (planeWords.toList.getD 2 [])) wd.W = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
