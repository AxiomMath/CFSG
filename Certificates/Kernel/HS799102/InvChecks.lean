module

public import Certificates.Kernel.HS799102.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KC.Misc.ArrEnum

theorem ch799102_ibind : (rGBind && allN 6 (fun k => permB 100 7 (rG k))) = true := by quickRfl

theorem ch799102_ip0 : (pointOrbK 100 7 rG 6 0 P0 && Nat.beq P0.length 100) = true := by
  quickRfl

theorem ch799102_ihg : (wordsK hG HW 3 &&
    allN 3 (fun k => Nat.beq (pg 7 (CFSG.KS.mask 7) (hG k) 0) 0)) = true := by quickRfl

theorem ch799102_ing : (wordsK nG NW 3 && allN 3 (fun k => Nat.beq (pg 7 (CFSG.KS.mask 7) (nG k) 0) 0 &&
    Nat.beq (imgM 100 7 (nG k) SM) SM)) = true := by quickRfl

theorem ch799102_inl : (mulRecK 100 7 nG 3 NL && Nat.beq NL.length 144 &&
    Nat.beq SR.length 6160) = true := by quickRfl

theorem ch799102_iv : (ivK && fixK && smK) = true := by quickRfl

theorem ch799102_iscan : scanK = true := by quickRfl

end CertificateChecks.KernelHS799102

end
