module

public import Certificates.Kernel.LyY.ChainLv
public import Certificates.Kernel.LyY.ChainSchA
public import Certificates.Kernel.LyY.ChainSchB
public import Certificates.Kernel.LyY.ChainSchC
public import Certificates.Kernel.LyTr.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelLyY.YC

namespace CertificateChecks.KernelLyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem k_ties : bAnd(Nat.beq (YC.S 0) (CertificateChecks.KernelLyTr.UH.F 0),
    bAnd(Nat.beq (YC.S 1) (CertificateChecks.KernelLyTr.UH.F 3),
    bAnd(Nat.beq (rcnt (YC.LR 0)) 1080, bAnd(Nat.beq (rcnt (YC.LR 1)) 54,
    bAnd(Nat.beq (rcnt (YC.LR 2)) 6,
      allN 8 (fun j => permOK 1080 11 (mask 11) (1080 * 11) (YC.S j) (YC.SI j))))))) = true := by
  quickRfl

end CertificateChecks.KernelLyY

end
