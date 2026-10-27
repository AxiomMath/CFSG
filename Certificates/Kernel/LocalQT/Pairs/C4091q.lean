module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

theorem kQe : CFSG.KC.LQT.P.allL Q1E (fun q => Nat.beq (sqW 315 9 q 2) (oneW 315 9)) = true := by
  quickRfl
theorem kAe : CFSG.KC.LQT.P.allL A2X' (fun q => Nat.beq (sqW 315 9 q 2) (oneW 315 9)) = true := by
  quickRfl
theorem kA1 : CFSG.KC.LQT.S.memL (oneW 315 9) A2X' = true := by quickRfl
theorem kz1 : CFSG.KC.LQT.P.allL K1G (fun g => CFSG.KC.LQT.P.allL A1E fun a =>
    CFSG.KC.Ord.andB (CFSG.KC.LQT.S.memL (conjW 315 9 g a) A1E)
      (CFSG.KC.LQT.S.memL (conjIW 315 9 g a) A1E)) = true := by quickRfl
theorem kQn : CFSG.KC.LQT.P.allL K1G (fun g => CFSG.KC.LQT.P.allL Q1E fun a =>
    CFSG.KC.Ord.andB (CFSG.KC.LQT.S.memL (conjW 315 9 g a) Q1E)
      (CFSG.KC.LQT.S.memL (conjIW 315 9 g a) Q1E)) = true := by quickRfl
theorem kN2 : CFSG.KC.LQT.P.allL K2G (fun g => CFSG.KC.LQT.P.allL A2X' fun a =>
    CFSG.KC.Ord.andB (CFSG.KC.LQT.S.memL (conjW 315 9 g a) A2X')
      (CFSG.KC.LQT.S.memL (conjIW 315 9 g a) A2X')) = true := by quickRfl
theorem kF1 : CFSG.KC.LQT.P.allL K1G (fun g => Nat.beq (imgMaskW 315 9 g F1M) F1M) = true := by
  quickRfl
theorem kF2 : CFSG.KC.LQT.P.allL K2G (fun g => Nat.beq (imgMaskW 315 9 g F2M) F2M) = true := by
  quickRfl

end CFSG.KD.LQT.C4091

end
