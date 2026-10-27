module

public import Certificates.Kernel.LyY.ChainData
public import Certificates.Kernel.LyY.ScanData
public import Certificates.Kernel.LyTr.Data
public import Certificates.Data.Kernel.LyY.Orb
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.LyY CFSG.KC.Child3

@[expose] noncomputable def xoP : Nat := codeProd 1080 11 YC.LR YC.TR XO

theorem k_ca : clsOK 1080 11 YC.LR YC.TR YC.TRI YC.BP (YC.S 0) CA 2430 = true := by quickRfl

theorem k_co : strictB xoP (fun X => clsOK 1080 11 YC.LR YC.TR YC.TRI YC.BP X CO 81) = true := by
  quickRfl

theorem k_fix : bAnd(codeOK YC.LR XO, strictB xoP (fun X =>
    bAnd(allN 1080 (fun p => Nat.beq (pg 11 (mask 11) X (pg 11 (mask 11) X p)) p),
    bAnd(Nat.beq (fixCnt 1080 (fun p => pg 11 (mask 11) X p)) 120,
      Nat.beq (fixCnt 1080 (fun p => pg 11 (mask 11) (YC.S 0) p)) 40)))) = true := by
  quickRfl

theorem k_orb : orbOK 1080 11 CertificateChecks.KernelLyTr.R1.GI 5 7 TL TP TG TD = true := by
  quickRfl

theorem k_lbl : bAnd(Nat.beq (lblCnt 1080 TL 0) 648, bAnd(Nat.beq (lblCnt 1080 TL 1) 324,
    bAnd(Nat.beq (lblCnt 1080 TL 2) 24, bAnd(Nat.beq (lblCnt 1080 TL 3) 24,
    bAnd(Nat.beq (lblCnt 1080 TL 4) 24, bAnd(Nat.beq (lblCnt 1080 TL 5) 24,
      Nat.beq (lblCnt 1080 TL 6) 12)))))) = true := by
  quickRfl

theorem k_img : imgOK 1080 11 (YC.S 0) (YC.S 1) TL 6 OS OP OG 90 = true := by quickRfl

theorem k_dist : distinctOK 11 OS 90 = true := by quickRfl

end CertificateChecks.KernelLyY

end
