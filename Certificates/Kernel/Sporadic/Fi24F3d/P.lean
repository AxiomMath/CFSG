module

public import Certificates.Kernel.Sporadic.Fi24F3d.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.Fi24F3d

open CFSG.KC.Fi24Kn CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb CFSG.KC.Fi24G2d

theorem P.lE : fixLOK LE CFSG.KD.Fi24Fix.TG WE 306936 36 = true := by quickRfl

theorem P.lEF : fixLOK LEF CFSG.KD.Fi24Fix.TG WEF 306936 36 = true := by quickRfl

theorem P.lY : fixLOK LY CFSG.KD.Fi24Fix.TG WY 306936 21 = true := by quickRfl

theorem P.kE : knOK CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Orb.FD LE (nthN J.AE) (nthN J.BE) (nthW J.CE)
    9 36 = true := by quickRfl

theorem P.kEF : knOK CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Orb.FD LEF (nthN J.AEF) (nthN J.BEF)
    (nthW J.CEF) 9 36 = true := by quickRfl

theorem P.kY : knOK CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Orb.FD LY (nthN J.AY) (nthN J.BY) (nthW J.CY)
    7 21 = true := by quickRfl

theorem P.wE : ∀ w ∈ J.CE, (∀ g ∈ w, g < 12) ∧ w.length % 2 = 0 := by decide +kernel

theorem P.wEF : ∀ w ∈ J.CEF, (∀ g ∈ w, g < 12) ∧ w.length % 2 = 0 := by decide +kernel

theorem P.wY : ∀ w ∈ J.CY, (∀ g ∈ w, g < 12) ∧ w.length % 2 = 0 := by decide +kernel

theorem P.root : Nat.beq (walk CFSG.KD.Fi24Fix.TG C0 (CFSG.KD.Fi24Orb.NM 0)) 0 = true := by
  quickRfl

theorem P.s1 : Nat.beq (walk CFSG.KD.Fi24Fix.TG C0
    (walk CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.AW (CFSG.KD.Fi24Orb.NM 0))) 6983 = true := by quickRfl

theorem P.c1 : Nat.beq (fComp (CFSG.KD.Fi24Orb.FD 6983)) 2 = true := by quickRfl

theorem P.mvE : negB (Nat.beq (walk CFSG.KD.Fi24Fix.TG WE 6) 6) = true := by quickRfl

theorem P.mvY : negB (Nat.beq (walk CFSG.KD.Fi24Fix.TG WY 1) 1) = true := by quickRfl

theorem P.fE : Nat.beq (walk CFSG.KD.Fi24Fix.TG WE 1) 1 = true := by quickRfl

theorem P.mF : negB (Nat.beq (walk CFSG.KD.Fi24Fix.TG WF 1) 1) = true := by quickRfl

theorem P.aw : negB (Nat.beq (walk CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.AW (CFSG.KD.Fi24Orb.NM 0))
    (CFSG.KD.Fi24Orb.NM 0)) = true := by quickRfl

end CFSG.KD.Fi24F3d

end
