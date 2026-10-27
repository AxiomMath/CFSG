module

public import Certificates.Kernel.LocalComp.McLYW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.McLY.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.LocalComp.ConjPin CFSG.KC.LocalComp.Pin
open CFSG.KC.LocalComp.Perm

theorem inv : (!invTabK 11 yG[0]! yG[1]!) = true := by decide +kernel

theorem perm : (!permK 11 #[0, 10, 6, 2, 7, 5, 3, 9, 1, 4, 4]) = true := by decide +kernel

theorem orb : (!bfsCK 11 4 YE.ng YE.G YGI (YX 1) (ySz 0) (fun p => YA (yOff 0 + p))
    (fun p => YAE (yOff 0 + p)) (fun p => YAS (yOff 0 + p))) = true := by
  decide +kernel

theorem notIn : (!notInK 11 4 (ySz 1) (fun p => YA (yOff 1 + p)) (YX 1)) = true := by
  decide +kernel

end CertificateChecks.KernelLC.McLY.Neg

end
