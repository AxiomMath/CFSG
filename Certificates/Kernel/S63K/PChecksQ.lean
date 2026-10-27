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

#kc_each CertificateChecks.KernelS63.PD.ch4237V 0 64
#kc_each CertificateChecks.KernelS63.PD.ch4237C 0 64
#kc_each CertificateChecks.KernelS63.PD.ch4237Q 0 8
#kc_each CertificateChecks.KernelS63.PD.ch4237U 0 13

theorem qinT : (allN 8 fun k => Nat.beq (memS HD.TP HD.TS 4096 (AD.QG k % 2 ^ 576)) 1) = true := by
  quickRfl

theorem t0Q : Nat.beq (memS AD.QP AD.QS 512 T0r) 1 = true := by quickRfl

theorem v : vK = true := by quickRfl

theorem zcbfs : bfsK (cjStepK CD.CG) ZCP ZCPar ZCLab ZCW ZCS 4 (3 + 1) 3 (ID.ZP 0) = true := by
  quickRfl

theorem ucbfs : bfsK (cjStepK CD.CG) UCP UCPar UCLab UCW UCS 4 (24 + 1) 24 (U0 0) = true := by
  quickRfl

theorem steps : CFSG.D4Hex.locStepWords.all stepOKK = true := by quickRfl

theorem cwfix : CFSG.LargeExtraspecial.S63.cWords.all (fun w => stepOKK (false, w)) = true := by
  quickRfl

theorem pw : pwK = true := by quickRfl

theorem vneg : bAnd(bIf(bfsK (cjStepK CD.CG) ZCP ZCPar ZCLab ZCW ZCS 4 (3 + 1) 3 (ID.ZP 1), false,
      true),
    bAnd(bIf(invK (AD.QP 0), false, true),
      bIf(Nat.beq (memS AD.QP AD.QS 512 (HD.TP (QB (QK 0)))) 1, false, true))) = true := by
  quickRfl

end CertificateChecks.KernelS63.PD

end
