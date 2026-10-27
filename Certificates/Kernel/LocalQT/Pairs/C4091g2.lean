module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

theorem gK21 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK K2P) = true := by quickRfl
theorem gK22 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN K2E) = true := by quickRfl
theorem gK24 : depthOK K2G K2P 40 = true := by quickRfl
theorem gK25 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN (List.map (hkW 315 9) K2E)) = true := by
  quickRfl
theorem lK2 : Nat.beq (CFSG.KC.LQT.S.lenL K2E) 1152 = true := by quickRfl

end CFSG.KD.LQT.C4091

end
