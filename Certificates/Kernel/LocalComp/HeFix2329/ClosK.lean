module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.LocalComp.HeFix2329.Data
public import Certificates.Data.Kernel.HeFixK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeFix2329

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermTool CFSG.KC.HeFixK
open CertificateChecks.KernelLC.HeFix

theorem kClos0 : closK 8330 14 5 2048 SA SB SM (Q 0) (T0K 0) 0 = true := by quickRfl

theorem kClos1 : closK 8330 14 5 2048 SA SB SM (Q 1) (T0K 1) 1 = true := by quickRfl

theorem kClos2 : closK 8330 14 5 2048 SA SB SM (Q 2) (T0K 2) 2 = true := by quickRfl

theorem kClos3 : closK 8330 14 5 2048 SA SB SM (Q 3) (T0K 3) 3 = true := by quickRfl

theorem kClos4 : closK 8330 14 5 2048 SA SB SM (Q 4) (T0K 4) 4 = true := by quickRfl

theorem kClos5 : closK 8330 14 5 2048 SA SB SM (Q 5) (T0K 5) 5 = true := by quickRfl

theorem kFix : Nat.beq (fixK 8330 14 (wordTabK 8330 14 T0K [3, 2])) 346 = true := by quickRfl

theorem kCanonQ : allN 6 (fun j => canonK 32 6 (mask 6) (32 * 6) (Q j)) = true := by quickRfl

end CertificateChecks.KernelLC.HeFix2329

end
