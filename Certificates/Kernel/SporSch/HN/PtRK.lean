
module

public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.StrongK
public import Certificates.Data.Kernel.SporSch.HNXPt
public import Certificates.Data.Kernel.SporSch.HNXPrim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPtR

open CFSG.KC.LL.HNX CFSG.KS.SporSch CertificateChecks.KernelSporSch.HNStrong

@[expose] noncomputable def sIdx (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 34), Nat.add (nat_lit 13) c, Nat.sub c (nat_lit 34))

theorem valid_R : CFSG.KC.Enum.allN 36 (fun c => validHN (CFSG.KD.HNPt.R c)) = true := by
  quickRfl

theorem bridge_R :
    CFSG.KC.Enum.allN 36 (fun c => lanesEq (CFSG.KD.HNPt.R c) (ss (sIdx c))) = true := by
  quickRfl

theorem neg_bridge : Bool.not (lanesEq (CFSG.KD.HNPt.R 0) (ss 14)) = true := by quickRfl
theorem neg_valid : Bool.not (validHN (Nat.add (CFSG.KD.HNPt.R 0) 5)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPtR

end
