module

public import Certificates.Kernel.G24Th799103.MData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KC.Misc.ArrEnum CertificateChecks.KernelG24.Tri27206

theorem ch799103_mq0 : (pointOrbK 1365 11 xyG 2 Y0 Q0 && Nat.beq Q0.length 1365) = true := by
  quickRfl

theorem ch799103_mag : (Nat.beq AG.length 3 && allN 3 (fun k => permB 1365 11 (aG k) &&
    inDK (aG k) && Nat.beq (pg 11 (CFSG.KS.mask 11) (aG k) Y0) Y0)) = true := by quickRfl

theorem ch799103_mtm : (fixMK (TG.F 2) TM && Nat.testBit TM Y0 && Nat.beq (popK TM) 63 &&
    Nat.beq ST.length 960) = true := by quickRfl

theorem ch799103_mmem : allN 2 (fun k => permB 1365 11 (mG k) && inDK (mG k) &&
    commPt (mG k) (TG.F 2)) = true := by quickRfl

theorem ch799103_mdg : (Nat.beq (dG 0) (commP 1365 11 (mG 0) (mG 1)) &&
    Nat.beq (dG 1) (commP 1365 11 (mG 0) (mulG (mG 0) (mG 1)))) = true := by quickRfl

theorem ch799103_mn : (stabLowK 1365 11 mG 2 NM && baseInK NM (maskK RO) &&
    Nat.beq ((NM.map fun lv => lv.2.2.2.length).prod) 12096) = true := by quickRfl

theorem ch799103_mo : oddOrbK 1365 11 dG 2 XO (maskK RO) RO = true := by quickRfl

theorem ch799103_mw : normK 1365 11 mG 2 dG 2 WM = true := by quickRfl

end CertificateChecks.KernelG24Th

end
