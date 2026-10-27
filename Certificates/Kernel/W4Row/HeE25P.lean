module

public import Certificates.Data.Kernel.W4Row.EPackK
public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.W4Row.HeE25W
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.W4E.HeE25

open CFSG.KC.Enum CFSG.KS CFSG.KC.W4E CertificateChecks.KernelLC.HeFix

theorem invs : (permOK 8330 14 (mask 14) (8330 * 14) (HG.F 0) (HG.F 0) &&
    permOK 8330 14 (mask 14) (8330 * 14) PT1 PT1 && permOK 8330 14 (mask 14) (8330 * 14) PU PU) =
    true := by
  quickRfl

theorem pack : e25PackK 8330 14 (pidn 8330 14) (W 0) (W 2) (W 4) (W 5) (W 6) (W 7) (W 8) (W 9)
    (W 10) (W 11) (W 12) (W 13) = true := by
  quickRfl

theorem conj0 : conjInvK 8330 14 (HG.F 0) (HG.F 0) (W 14) (W 15) (W 0) (W 1) = true := by
  quickRfl

theorem conj1 : conjInvK 8330 14 PT1 PT1 (W 16) (W 17) (W 0) (W 1) = true := by
  quickRfl

theorem conjU : conjInvK 8330 14 PU PU (W 18) (W 19) (W 0) (W 1) = true := by
  quickRfl

end CFSG.KD.W4E.HeE25

end
