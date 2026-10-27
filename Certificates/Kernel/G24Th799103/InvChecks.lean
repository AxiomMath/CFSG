module

public import Certificates.Kernel.G24Th799103.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KC.Misc.ArrEnum CertificateChecks.KernelG24.Tri27206

theorem ch799103_iperm : (allN 3 (fun k => permB 1365 11 (TG.F k)) &&
    allN 3 (fun k => permB 1365 11 (rG k))) = true := by quickRfl

theorem ch799103_ip0 : (pointOrbK 1365 11 rG 3 X0 P0 && Nat.beq P0.length 1365) = true := by
  quickRfl

theorem ch799103_ihg : (Nat.beq HG.length 3 && allN 3 (fun k => permB 1365 11 (hG k) &&
    inRK (hG k) (HT.getD k 0) && Nat.beq (pg 11 (CFSG.KS.mask 11) (hG k) X0) X0)) = true := by
  quickRfl

theorem ch799103_ikg : (Nat.beq KG.length 3 && allN 3 (fun k => permB 1365 11 (kG k) &&
    inRK (kG k) (KT.getD k 0) && Nat.beq (pg 11 (CFSG.KS.mask 11) (kG k) X0) X0 &&
    Nat.beq (imgM 1365 11 (kG k) DM) DM)) = true := by quickRfl

theorem ch799103_ing : (Nat.beq NG.length 3 && allN 3 (fun k => permB 1365 11 (nG k) &&
    inRK (nG k) (NT.getD k 0) && Nat.beq (imgM 1365 11 (nG k) DM) DM &&
    Nat.beq (imgM 1365 11 (nG k) FM) FM)) = true := by quickRfl

theorem ch799103_imask : (fixMK (mulG (TG.F 0) (mulG (TG.F 1) (TG.F 1))) DM &&
    fix2MK (TG.F 0) (TG.F 1) FM && Nat.testBit FM X0 && Nat.beq (Nat.land DM FM) FM &&
    Nat.beq (Nat.add EM FM) DM && Nat.beq (popK FM) 6) = true := by quickRfl

theorem ch799103_itau : (Nat.beq (mulG (TG.F 2) (TG.F 2)) (pidn 1365 11) &&
    inDK (mulG (TG.F 2) (mulG (LC.S 0) (TG.F 2))) &&
    inDK (mulG (TG.F 2) (mulG (LC.S 1) (TG.F 2)))) = true := by quickRfl

theorem ch799103_inl : (mulRecK 1365 11 nG 3 NL && Nat.beq NL.length 216 &&
    Nat.beq SR.length 64 && Nat.beq SF.length 160) = true := by quickRfl

theorem ch799103_iscan : allL invT (NL.map Prod.fst) = true := by quickRfl

end CertificateChecks.KernelG24Th

end
