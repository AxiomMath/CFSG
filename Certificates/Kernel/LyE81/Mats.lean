module

public import Certificates.Kernel.LyE81.Data
public import Certificates.Kernel.SporSch.Ly.BSData
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporLyE81Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLitToList
import Mathlib.Tactic.IntervalCases
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyE81

open CFSG.KD.LyE81 CFSG.KD.LyS0 CFSG.KC.Enum CFSG.RankThree.PartTwo.Sec4.Item434SporLy

local notation "A0" => CertificateChecks.KernelSporSch.LyBS.A

local notation "B0" => CertificateChecks.KernelSporSch.LyBS.B

theorem slp1 : Nat.beq (CFSG.KD.LyS0.mul (CFSG.KD.LyS0.mul (pw (slpR6 A0 B0) 15) A0)
    (pw (slpR6 A0 B0) 52)) C = true := by quickRfl

theorem slp2 : Nat.beq (CFSG.KD.LyS0.mul (CFSG.KD.LyS0.mul (pw (slpR9 A0 B0) 55) (slpR2 A0 B0))
    (pw (slpR9 A0 B0) 12)) D = true := by quickRfl

theorem slp3 : Nat.beq (CFSG.KD.LyS0.mul (pw (slpR6 A0 B0) 15) (pw (slpR6 A0 B0) 52))
    CFSG.KD.OrdLy.ONE = true := by quickRfl

theorem slp4 : Nat.beq (CFSG.KD.LyS0.mul (pw (slpR9 A0 B0) 12) (pw (slpR9 A0 B0) 55))
    CFSG.KD.OrdLy.ONE = true := by quickRfl

theorem words : ∀ k < 7, wordK CD (lyE81.pW[k]!) = PK k := by
  intro k hk
  simp only [lyE81, cdWord, CFSG.KC.StrLitToList.strLitToList]
  interval_cases k <;> exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem letters : lyE81.pW.toList.all (fun w => w.all fun x => decide (x.1 < 2)) = true := by
  simp only [lyE81, cdWord, CFSG.KC.StrLitToList.strLitToList]
  decide

theorem pWsz : lyE81.pW.size = 7 := rfl

theorem fuelEq : lyE81.fuel = 2200 := rfl

theorem vEq : (List.range 111).all (fun j => Nat.beq (ln (V 0) j) (lyE81.v[j]!)) = true := by
  quickRfl

theorem vSz : lyE81.v.size = 111 := rfl

theorem pc : pcK PK lyE81.cubeW lyE81.commW = true := by quickRfl

theorem tr : allBlk 0 (fun k => trK (PK k) (PT k)) 7 = true := by quickRfl

theorem vM : allBlk 0 (fun k => vld (MI k)) 16 = true := by quickRfl

end CertificateChecks.KernelLyE81

end
