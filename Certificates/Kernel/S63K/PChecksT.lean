module

public import Certificates.Kernel.S63K.PDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.Kernel.S63K.OrbRun

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.PD

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CertificateChecks.KernelS63

theorem words : wordsK = true := by quickRfl

theorem fbound : (allN 495 fun i => Nat.blt (FO i) 4096) = true := by quickRfl

theorem froots : bAnd(Nat.beq (HD.TP (FO 0)) (ID.ZP 0), Nat.beq (HD.TP (FO 1)) T0r) = true := by
  quickRfl

theorem fdist : bfsDistK FO FS 495 = true := by quickRfl

theorem frun : Nat.beq (orbRunK FW FPa FLa 12 (495 + 1) 0 2) 495 = true := by quickRfl

#kc_each CertificateChecks.KernelS63.PD.ch4237F 0 15
#kc_each CertificateChecks.KernelS63.PD.ch4237I 0 64
#kc_each CertificateChecks.KernelS63.PD.ch4237Z 0 64

theorem neg : bAnd(bIf(Nat.beq (HD.TP (FO 1)) (HD.TP (FO 0)), false, true),
    bAnd(bIf(invK (HD.TP 0), false, true),
      bIf(Nat.beq (orbRunK FW FPa (fun i => FLa i + 1) 12 (495 + 1) 0 2) 495, false, true))) =
    true := by
  quickRfl

end CertificateChecks.KernelS63.PD

end
