module

public import Certificates.Kernel.LocalQT.Pairs.C4094h
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4094

open CFSG.KC.LQT.PH CFSG.KD.LQT.M24K

@[expose] noncomputable def clB (k : Nat) : Bool :=
  blkRange (CFSG.KC.LQT.P.conj 24) zC GAB 128 (CFSG.KC.LQT.S.lenL (flatB CFSG.KD.LQT.M24Class.B))
    CFSG.KD.LQT.M24Class.B CFSG.KD.LQT.M24Class.T (k * 8) 8

theorem cS : sortedB 128 CFSG.KD.LQT.M24Class.B = true := by quickRfl
theorem cZ : memB zC CFSG.KD.LQT.M24Class.B = true := by quickRfl
theorem cN : Nat.beq (CFSG.KC.LQT.S.lenL (flatB CFSG.KD.LQT.M24Class.B)) 11385 = true := by quickRfl
theorem cK : Nat.beq (CFSG.KC.LQT.L.lenA CFSG.KD.LQT.M24Class.B) 89 = true := by quickRfl
theorem ch0 : hkB CFSG.KD.LQT.M24Class.B 3 0 = true := by quickRfl
theorem ch1 : hkB CFSG.KD.LQT.M24Class.B 3 1 = true := by quickRfl
theorem ch2 : hkB CFSG.KD.LQT.M24Class.B 3 2 = true := by quickRfl

end CFSG.KD.LQT.C4094

#kon_slices CFSG.KD.LQT.C4094.clB 0 12

end
