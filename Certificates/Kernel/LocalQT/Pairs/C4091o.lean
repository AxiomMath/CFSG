module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

noncomputable abbrev O1E : List Nat := orbE GAB F1M O1P
noncomputable abbrev O2E : List Nat := orbE GAB F2M O2P

theorem o11 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK O1P) = true := by quickRfl
theorem o12 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN O1E) = true := by quickRfl
theorem o13 : closedM GAB O1E = true := by quickRfl
theorem o1N : Nat.beq (CFSG.KC.LQT.S.lenL O1E) 315 = true := by quickRfl
theorem o1L : CFSG.KC.LQT.L.allA (CFSG.KC.LQT.Syl.pairUpK O1P)
    (fun q => Nat.blt q.2 (CFSG.KC.LQT.L.lenA GAB)) = true := by quickRfl
theorem o21 : CFSG.KC.LQT.T2.monoK (CFSG.KC.LQT.Syl.pairUpK O2P) = true := by quickRfl
theorem o2L : CFSG.KC.LQT.L.allA (CFSG.KC.LQT.Syl.pairUpK O2P)
    (fun q => Nat.blt q.2 (CFSG.KC.LQT.L.lenA GAB)) = true := by quickRfl
theorem o22 : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN O2E) = true := by quickRfl
theorem o23 : closedM GAB O2E = true := by quickRfl
theorem o2N : Nat.beq (CFSG.KC.LQT.S.lenL O2E) 525 = true := by quickRfl
theorem lA2 : Nat.beq (CFSG.KC.LQT.S.lenL A2E) 64 = true := by quickRfl

end CFSG.KD.LQT.C4091

end
