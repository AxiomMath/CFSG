module

public import Certificates.Kernel.Misc.Perm.HS100.X3ClsData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.HS100.X3Cls

open CFSG.KC.PCent
open CFSG.KC.Enum (pg pcomp allN)
open CFSG.KS (mask)

theorem x3Cls_ok : classK 100 7 pG pGI 3 v R = true := by quickRfl

theorem x3Cls_bind : (allN 3 (fun k => Nat.beq (pG k) (wordK 100 7 hsW (W.getD k [])) &&
    allL (fun c => Nat.blt c 6) (W.getD k []) && Nat.beq (pg 7 (mask 7) (pG k) p) p) &&
    Nat.beq v (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (HX.F 0) (HX.F 15))
      (pcomp 100 7 (mask 7) (HX.F 0) (HX.F 15)))) = true := by quickRfl

theorem x3Cent_ok : stabLowK 100 7 pC 4 L = true := by quickRfl

theorem x3Cent_len : Nat.beq (L.map fun lv => lv.2.2.2.length).prod 720 = true := by quickRfl

theorem x3Cent_bind : allN 4 (fun k => Nat.beq (pC k) (wordK 100 7 hsW (CW.getD k [])) &&
    allL (fun c => Nat.blt c 6) (CW.getD k []) &&
    Nat.beq (pcomp 100 7 (mask 7) (pC k) v) (pcomp 100 7 (mask 7) v (pC k))) = true := by quickRfl

theorem x3Cls_len : (Nat.beq R.length 12320 && Nat.beq (pg 7 (mask 7) v p) p) = true := by quickRfl

theorem x3Perm : allN 3 (fun k => CFSG.KC.Misc.ArrEnum.permB 100 7 (hsW k)) = true := by quickRfl

theorem x3Pt_ok : (pointOrbK 100 7 hsW 2 p PO && Nat.beq PO.length 100) = true := by quickRfl

theorem x3Cls_wAB : allN 3 (fun k => allL (fun c => Nat.blt c 2 || Nat.beq c 3 || Nat.beq c 4)
    (W.getD k [])) = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.X3Cls

end
