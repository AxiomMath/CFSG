module

public import Certificates.Data.Kernel.J4FixK
public import Certificates.Kernel.LocalComp.J4Rows

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.J4Fix

open CFSG.KC.J4Fix CertificateChecks.KernelLC.J4R

set_option maxHeartbeats 0 in
theorem central_K : fixCentralK 112 (zK JA.M JB.M) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem powXY_K : powXYK 112 (xK JA.M JB.M) (yK JA.M JB.M) = true := by decide +kernel

theorem h40_K : Nat.beq (CFSG.KC.OpsF2K.powK 112 (hK JA.M JB.M) 40) (CFSG.KC.M1F2.idF 112) =
    true := by
  decide +kernel

theorem conjX_K : CFSG.KC.OpsF2K.conjK 112 (hK JA.M JB.M) (xK JA.M JB.M)
    (CFSG.KC.M1F2.mulF 112 (CFSG.KC.M1F2.mulF 112 (powLK 112 (xK JA.M JB.M) 0)
      (powLK 112 (yK JA.M JB.M) 7)) (powLK 112 (zK JA.M JB.M) 1)) = true := by
  decide +kernel

theorem conjY_K : CFSG.KC.OpsF2K.conjK 112 (hK JA.M JB.M) (yK JA.M JB.M)
    (CFSG.KC.M1F2.mulF 112 (CFSG.KC.M1F2.mulF 112 (powLK 112 (xK JA.M JB.M) 6)
      (powLK 112 (yK JA.M JB.M) 9)) (powLK 112 (zK JA.M JB.M) 6)) = true := by
  decide +kernel

theorem conjZ_K : CFSG.KC.OpsF2K.conjK 112 (hK JA.M JB.M) (zK JA.M JB.M)
    (powLK 112 (zK JA.M JB.M) 2) = true := by
  decide +kernel

end CertificateChecks.KernelLC.J4Fix

end
