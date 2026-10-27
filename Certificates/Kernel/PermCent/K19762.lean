module

public import Certificates.Data.Kernel.PermCent.M11PairQ

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.M11B

theorem k19762_word : wordC = true := by decide +kernel

theorem k19762_countQ : pairCntQ = 7920 := by decide +kernel

theorem k19762_count : pairCntC = 7920 := pairCntQ_eq.symm.trans k19762_countQ

end CertificateChecks.KernelPermCent
