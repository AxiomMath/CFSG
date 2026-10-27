module

public import Certificates.Kernel.L34W.Tabs
public import Certificates.Kernel.L34W.Gens
public import Certificates.Data.Kernel.L34W.Outer
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.L34W.OutData

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelL34W.YT CertificateChecks.KernelL34W.yArr 6
#kmisc_packarrs CertificateChecks.KernelL34W.OT CertificateChecks.KernelL34W.otArr 12
#kmisc_packarrs CertificateChecks.KernelL34W.RK CertificateChecks.KernelL34W.rkArr 8
#kmisc_packarrs CertificateChecks.KernelL34W.CM CertificateChecks.KernelL34W.cmArr 1
#kmisc_packarrs CertificateChecks.KernelL34W.BT CertificateChecks.KernelL34W.btArr 10

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W

theorem y_k : yOK GT YT = true := by decide +kernel

theorem out_k : outOK YT OT RK = true := by decide +kernel

theorem comm_k : commOK YT OT CM = true := by decide +kernel

theorem beta_k : betaOK T1X.F AlX.F OT BT = true := by decide +kernel

theorem y_neg : (!yOK GT (patchT YT 2303 (pidn 42 6))) = true := by decide +kernel

theorem out_neg : (!outOK YT OT (patchT RK 2303 0)) = true := by decide +kernel

theorem comm_neg : (!commOK YT OT (patchT CM 143 (Nat.xor (CM 143) (Nat.shiftLeft 1 143)))) = true := by
  decide +kernel

theorem beta_neg : (!betaOK T1X.F AlX.F OT (patchT BT 143 (Nat.xor (BT 143) 1))) = true := by
  decide +kernel

end CertificateChecks.KernelL34W

end
