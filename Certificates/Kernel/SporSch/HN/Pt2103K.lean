module

public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.Pt2103Data
public import Certificates.Data.Kernel.SporSch.HNXPt
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2103

open CFSG.KC.LL.HNX CFSG.KD.HNPt2103 CFSG.KD.LgHNX

theorem w_K1 : Nat.beq (wordC CFSG.KD.HNPt.R k1c) K1 = true := by quickRfl
theorem w_K2 : Nat.beq (wordC CFSG.KD.HNPt.R k2c) K2 = true := by quickRfl
theorem w_C1 : Nat.beq (wordC CFSG.KD.HNPt.R c1c) C1 = true := by quickRfl
theorem w_S0 : Nat.beq (wordC CFSG.KD.HNPt.R s0c) S0 = true := by quickRfl

theorem t_K1 : Nat.beq (trM K1) TK1 = true := by quickRfl
theorem t_K2 : Nat.beq (trM K2) TK2 = true := by quickRfl
theorem t_S0 : Nat.beq (trM S0) TS0 = true := by quickRfl
theorem t_GK1 : Nat.beq (trM (CFSG.KC.LL.HN.subI K1)) GK1 = true := by quickRfl

theorem conj : Nat.beq (CFSG.KC.LL.HN.mm S0 K1) (CFSG.KC.LL.HN.mm C1 S0) = true := by quickRfl

theorem p_S0 : ptsImg TX MS CM3 M TS0 FL0 IL0 2 = true := by quickRfl
theorem p_K1 : ptsImg TX MS CM3 M TK1 F8 F8 8 = true := by quickRfl
theorem p_K2 : ptsImg TX MS CM3 M TK2 F8 U8 8 = true := by quickRfl

theorem neg_w : Bool.not (Nat.beq (wordC CFSG.KD.HNPt.R k2c) K1) = true := by quickRfl
theorem neg_conj : Bool.not (Nat.beq (CFSG.KC.LL.HN.mm S0 K2) (CFSG.KC.LL.HN.mm C1 S0)) = true := by
  quickRfl
theorem neg_pK2 : Bool.not (ptsImg TX MS CM3 M TK2 F8 F8 8) = true := by quickRfl
theorem neg_pS0 : Bool.not (ptsImg TX MS CM3 M TS0 FL0 FL0 2) = true := by quickRfl
theorem neg_fix : Bool.not (Nat.beq (fixSum TX CM3 M GK1 0 1) 0) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPt2103

end
