module

public import Certificates.Kernel.LocalComp.E8Tables
public import Certificates.Kernel.Om1K.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.SetOrb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1.A

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelLC.E8 (RT FT NEG)

theorem kRTv : allN 240 (fun r => permOK 240 8 (mask 8) (240 * 8) (RT r) (RT r)) = true := by
  quickRfl

theorem kFTv : allN 256 (fun m => permOK 240 8 (mask 8) (240 * 8) (FT m) (FT m)) = true := by
  quickRfl

theorem kNEGv : permOK 240 8 (mask 8) (240 * 8) NEG NEG = true := by quickRfl

end CertificateChecks.KernelOm1.A

end
