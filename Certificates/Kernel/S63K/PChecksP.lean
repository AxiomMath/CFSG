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

theorem qbound : (allN 2464 fun i => bAnd(Nat.blt (QA i) 4096, Nat.blt (QB i) 4096)) = true := by
  quickRfl

theorem qroot : bAnd(Nat.beq (HD.TP (QA 0)) (U0 0), Nat.beq (HD.TP (QB 0)) T0r) = true := by
  quickRfl

theorem qdist : bfsDistK qcode QS 2464 = true := by quickRfl

theorem qrun : Nat.beq (orbRunK QW QPa QLa 12 (2464 + 1) 0 1) 2464 = true := by quickRfl

theorem qk : bAnd(Nat.blt (QK 0) 2464, bAnd(Nat.beq (HD.TP (QA (QK 0))) (ID.ZP 0),
    Nat.beq (memS AD.QP AD.QS 512 (HD.TP (QB (QK 0)))) 0)) = true := by
  quickRfl

#kc_each CertificateChecks.KernelS63.PD.ch4237P 0 31

theorem qneg : bAnd(bIf(Nat.beq (memS AD.QP AD.QS 512 (ID.ZP 0)) 0, false, true),
    bAnd(bIf(Nat.beq (orbRunK QW QPa (fun i => QLa i + 1) 12 (2464 + 1) 0 1) 2464, false, true),
      bIf(Nat.beq (qcode 1) (qcode 0), false, true))) = true := by
  quickRfl

end CertificateChecks.KernelS63.PD

end
