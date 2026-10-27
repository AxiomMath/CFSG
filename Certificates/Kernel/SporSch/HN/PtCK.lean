module

public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.PtC
public import Certificates.Kernel.SporSch.HN.Invol2099K
public import Certificates.Data.Kernel.SporSch.HNXPt
public import Certificates.Data.Kernel.SporSch.HNXPrim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPtC

open CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KD.HNPtC

theorem valid_GT : CFSG.KC.Enum.allN 22 (fun c => validHN (GT c)) = true := by quickRfl

theorem w_GT : CFSG.KC.Enum.allN 10 (fun j => Nat.beq (wordC CFSG.KD.HNPt.R (gcF j)) (GT j)) =
    true := by quickRfl

theorem w_T4 : Nat.beq (wordC CFSG.KD.HNPt.R t4c) T4 = true := by quickRfl

theorem bridge_C : lanesEq (GT 10) (CertificateChecks.KernelSporSch.HNInvol.sx 36) = true := by
  quickRfl

theorem inv_GT : CFSG.KC.Enum.allN 11 (fun j =>
    Nat.beq (CFSG.KC.LL.HN.mm (GT j) (GT (Nat.add 11 j))) CFSG.KD.OrdHN.ONE) = true := by quickRfl

theorem neg_w : Bool.not (Nat.beq (wordC CFSG.KD.HNPt.R (gcF 1)) (GT 0)) = true := by quickRfl
theorem neg_C : Bool.not (lanesEq (GT 9) (CertificateChecks.KernelSporSch.HNInvol.sx 36)) = true :=
  by quickRfl
theorem neg_inv : Bool.not (Nat.beq (CFSG.KC.LL.HN.mm (GT 0) (GT 12)) CFSG.KD.OrdHN.ONE) = true :=
  by quickRfl

end CertificateChecks.KernelSporSch.HNPtC

end
