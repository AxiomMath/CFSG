module

public import Certificates.Data.Kernel.Sp62F.FastDefs
public import Certificates.Kernel.Sp62F.DataN
public import Certificates.Kernel.Sp62L.Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelSp62F

open CFSG.KD.Sp62W CFSG.KD.Sp62F CFSG.KD.BfsK CertificateChecks.KernelSp62L

#kc_each CertificateChecks.KernelSp62F ch9452kP (fun j => nBlkK NR 15 (SD.EB.map numC) j) 0 27

#kc_forall_chunks ch9452k_p (fun j => nBlkK NR 15 (SD.EB.map numC) j = true) 27
  CertificateChecks.KernelSp62F.ch9452kP 1

theorem ch9452k_n1 : nBlkK NR 15 [] 0 = false := by decide +kernel

end CertificateChecks.KernelSp62F

end
