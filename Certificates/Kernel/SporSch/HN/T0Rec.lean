module

public import Certificates.Kernel.SporSch.HN.T0Data
public import Certificates.Data.Kernel.Spor.EnumBase
public import Certificates.Data.Kernel.BfsPinBase
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KD.HNT0 CFSG.KS.EnumBase

#kc_each CertificateChecks.KernelSporSch.HNT0 ch10509r
  (fun s => sliceK 16384 64 (recK 192 8 255 4 G T PL) s) 0 256

theorem keys : CFSG.KC.BfsPin.keysSK 192 8 BP 16384 T SK = true := by quickRfl

theorem neg_rec : Bool.not (recK 192 8 255 4 (fun j => G (Nat.succ j)) T PL 1) = true := by quickRfl
theorem neg_keys : Bool.not (CFSG.KC.BfsPin.keysSK 192 8 BP 16384 (fun _ => T 0) SK) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNT0

end
