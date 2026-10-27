module

public import Certificates.Kernel.L34W.Outer
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Data.Kernel.L34W.RealB
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.L34W.RealBData

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelL34W.RBH CertificateChecks.KernelL34W.rbHdr 64
#kmisc_packarrs CertificateChecks.KernelL34W.RBW CertificateChecks.KernelL34W.rbArr 16

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W CertificateChecks.KernelLC

theorem ch22220k_0 : cK T1X.F AlX.F YT RBH RBW 0 1 0 4369 = true := by decide +kernel

theorem ch22220k_1 : cK T1X.F AlX.F YT RBH RBW 1 0 1 15 = true := by decide +kernel

theorem ch22220k_2 : cK T1X.F AlX.F YT RBH RBW 2 1 1 33825 = true := by decide +kernel

theorem ch22220k_3 : cK T1X.F AlX.F YT RBH RBW 3 1 2 16705 = true := by decide +kernel

theorem ch22220k_4 : cK T1X.F AlX.F YT RBH RBW 4 2 1 2565 = true := by decide +kernel

theorem ch22220k_5 : cK T1X.F AlX.F YT RBH RBW 5 1 3 9345 = true := by decide +kernel

theorem ch22220s_0 : repSK GT L34S.T 0 = true := by decide +kernel

theorem ch22220s_25 : repSK GT L34S.T 25 = true := by decide +kernel

theorem ch22220s_31 : repSK GT L34S.T 31 = true := by decide +kernel

theorem ch22220n_hdr : (!cK T1X.F AlX.F YT (patchT RBH 0 0) RBW 0 1 0 4369) = true := by
  decide +kernel

theorem ch22220n_w : (!cK T1X.F AlX.F YT RBH (fun _ => 0) 0 1 0 4369) = true := by decide +kernel

theorem ch22220n_s : (!repSK GT L34S.T 1) = true := by decide +kernel

end CertificateChecks.KernelL34W

end
