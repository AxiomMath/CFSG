module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

theorem gK11 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK K1P) = true := by quickRfl
theorem gK12 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN K1E) = true := by quickRfl
theorem gK14 : depthOK K1G K1P 40 = true := by quickRfl
theorem lK1 : Nat.beq (CFSG.KC.LQT.S.lenL K1E) 1920 = true := by quickRfl

end CFSG.KD.LQT.C4091

end
