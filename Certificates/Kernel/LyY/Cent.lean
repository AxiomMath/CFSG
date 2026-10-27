module

public import Certificates.Kernel.LyY.ChainData
public import Certificates.Kernel.LyY.ScanData
public import Certificates.Kernel.LyTr.Data
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.LyY.Cov
public import Certificates.Data.Kernel.LyY.Orb
public import CFSG.Sporadic.Recognition.LyonsAmalgamYInputs
meta import CFSG.Sporadic.Recognition.LyonsAmalgamYInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLyY.SG CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaHex
#kmisc_hexflat CertificateChecks.KernelLyY.SG CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaHex
  3 1080 11 1

public section

namespace CertificateChecks.KernelLyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LyY

theorem c_fix : allN 1080 (fun p => Nat.beq p 0 || !(allN 8 (fun j =>
    !(Nat.beq (pg 11 (mask 11) (YC.S j) 0) 0 && !(Nat.beq (pg 11 (mask 11) (YC.S j) p) p))))) =
    true := by
  quickRfl

theorem c_cov : Nat.beq (covN (fun k => pg 11 (mask 11) (YC.TR (roff 1080 (1080 * 11) (YC.LR 0) + k))
    0) 1080) (2 ^ 1080 - 1) = true := by
  quickRfl

theorem c_sift : bAnd(siftK 1080 11 (mask 11) (1080 * 11) (pidn 1080 11) YC.LR YC.TRI YC.BP 3 0
    (CertificateChecks.KernelLyTr.UH.F 1), bAnd(siftK 1080 11 (mask 11) (1080 * 11) (pidn 1080 11)
    YC.LR YC.TRI YC.BP 3 0 (CertificateChecks.KernelLyTr.UH.F 2),
    allN 5 (fun j => siftK 1080 11 (mask 11) (1080 * 11) (pidn 1080 11) YC.LR YC.TRI YC.BP 3 0
      (CertificateChecks.KernelLyTr.R1.GI j)))) = true := by
  quickRfl

theorem c_r1 : allN 5 (fun j => permOK 1080 11 (mask 11) (1080 * 11)
    (CertificateChecks.KernelLyTr.R1.GI j)
    (pinvS 1080 11 (mask 11) (CertificateChecks.KernelLyTr.R1.GI j))) = true := by
  quickRfl

theorem c_sig : bAnd(permOK 1080 11 (mask 11) (1080 * 11) (SG.F 0) (SG.F 0),
    !(allN 1080 (fun p => Nat.beq (lget TL (pg 11 (mask 11) (SG.F 0) p)) (lget TL p)))) = true := by
  quickRfl

theorem c_lbl : allN 1080 (fun p => bAnd(Nat.blt (lget TL p) 7,
    bIf(Nat.beq (lget TL p) 6, memN p (lgetL OS 0), !(memN p (lgetL OS 0))))) = true := by
  quickRfl

theorem c_neg : bAnd(bIf(Nat.beq (covN (fun k => pg 11 (mask 11)
    (YC.TR (roff 1080 (1080 * 11) (YC.LR 0) + k)) 0) 1079) (2 ^ 1080 - 1), false, true),
    bAnd(bIf(permOK 1080 11 (mask 11) (1080 * 11) (SG.F 0) (YC.S 0), false, true),
    bIf(allN 1080 (fun p => bIf(Nat.beq (lget TL p) 5, memN p (lgetL OS 0),
      !(memN p (lgetL OS 0)))), false, true))) = true := by
  quickRfl

end CertificateChecks.KernelLyY

end
