module

public import Certificates.Kernel.LyGlue.PtDefs

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims

theorem k_yBlk : (strictB (encW Ly0.wordU1) fun e0 => strictB (encW Ly0.wordU2) fun e1 =>
    strictB (encW Ly0.wordU3) fun e2 => strictB (encW Ly0.wordU4) fun e3 =>
    yBlkK e0 e1 e2 e3) = true := by
  decide +kernel

theorem k_tBlk : (strictB (encW (Glue.txWords.getD 0 [])) fun e0 =>
    strictB (encW (Glue.txWords.getD 1 [])) fun e1 =>
    strictB (encW (Glue.txWords.getD 2 [])) fun e2 =>
    strictB (encW (Glue.txWords.getD 3 [])) fun e3 =>
    tBlkK e0 e1 e2 e3) = true := by
  decide +kernel

theorem k_neg : (strictB (encW Ly0.wordU2) fun e1 => strictB (encW Ly0.wordU3) fun e2 =>
    strictB (encW Ly0.wordU4) fun e3 => yBlkK e1 e1 e2 e3) = false := by
  decide +kernel

end CertificateChecks.KernelLy

end
