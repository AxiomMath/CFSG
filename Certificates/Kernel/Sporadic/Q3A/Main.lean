
module

public import Certificates.Kernel.Sporadic.Q3A.Glue5
public import Certificates.Kernel.Sporadic.Q3A.KVt0
public import Certificates.Kernel.Sporadic.Q3A.KVt1
public import Certificates.Kernel.Sporadic.Q3A.KVt2
public import Certificates.Kernel.Sporadic.Q3A.KFr0
public import Certificates.Kernel.Sporadic.Q3A.KFr1
public import Certificates.Kernel.Sporadic.Q3A.KDs
public import Certificates.Kernel.Sporadic.Q3A.KQa
public import Certificates.Kernel.Sporadic.Q3A.KQb0
public import Certificates.Kernel.Sporadic.Q3A.KQb1

public section

#kon_join CertificateChecks.KernelSpor.Q3AK.vtAll CertificateChecks.KernelSpor.Q3AK.vtSl 143
#kon_join CertificateChecks.KernelSpor.Q3AK.frAll CertificateChecks.KernelSpor.Q3AK.frSl 143
#kon_join CertificateChecks.KernelSpor.Q3AK.ci0All CertificateChecks.KernelSpor.Q3AK.ci0 18
#kon_join CertificateChecks.KernelSpor.Q3AK.ci1All CertificateChecks.KernelSpor.Q3AK.ci1 4
#kon_join CertificateChecks.KernelSpor.Q3AK.ci2All CertificateChecks.KernelSpor.Q3AK.ci2 486
#kon_join CertificateChecks.KernelSpor.Q3AK.sp0All CertificateChecks.KernelSpor.Q3AK.sp0 18
#kon_join CertificateChecks.KernelSpor.Q3AK.sp1All CertificateChecks.KernelSpor.Q3AK.sp1 4
#kon_join CertificateChecks.KernelSpor.Q3AK.sp2All CertificateChecks.KernelSpor.Q3AK.sp2 486
#kon_join CertificateChecks.KernelSpor.Q3AK.qaAll CertificateChecks.KernelSpor.Q3AK.qa 486
#kon_join CertificateChecks.KernelSpor.Q3AK.qbAll CertificateChecks.KernelSpor.Q3AK.qb 486

namespace CertificateChecks.KernelSpor.Q3AG

open CFSG.Sporadic.SuzRecog.Q3A.Check CertificateChecks.KernelSpor.Q3AK

theorem hv : ∀ i < 22880, vtOK i = true := slices160 vtAll

theorem hf : ∀ i < 22880, frOK i = true := slices160 frAll

theorem hds : ∀ k < 3, dsChk k = true := by
  intro k hk
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · exact kDs0
  · exact kDs1
  · exact kDs2

theorem hci : ∀ k < 3, ∀ a < dlK k, ciSl k a = true := by
  intro k hk
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · exact ci0All
  · exact ci1All
  · exact ci2All

theorem hsp : ∀ k < 3, ∀ a < dlK k, spSl k a = true := by
  intro k hk
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · exact sp0All
  · exact sp1All
  · exact sp2All

theorem hq : ∀ k < 2, ∀ t < 486, q2Sl k t = true := by
  intro k hk
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact qaAll
  · exact qbAll

theorem q3aOK_true : q3aOK = true := q3aOK_of hv hf hds hci hsp hq

end CertificateChecks.KernelSpor.Q3AG

end
