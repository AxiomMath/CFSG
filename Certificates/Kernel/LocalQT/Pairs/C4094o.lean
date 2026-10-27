module

public import Certificates.Kernel.LocalQT.Pairs.C4094h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4094

open CFSG.KC.LQT.PH CFSG.KD.LQT.M24K

noncomputable abbrev trB (k : Nat) : Bool :=
  blkRange (actTK 24) tC GAB 128 (CFSG.KC.LQT.S.lenL (flatB CFSG.KD.LQT.M24Trio.B))
    CFSG.KD.LQT.M24Trio.B CFSG.KD.LQT.M24Trio.T (k * 8) 8

theorem oS : sortedB 128 CFSG.KD.LQT.M24Trio.B = true := by quickRfl
theorem oZ : memB tC CFSG.KD.LQT.M24Trio.B = true := by quickRfl
theorem oN : Nat.beq (CFSG.KC.LQT.S.lenL (flatB CFSG.KD.LQT.M24Trio.B)) 3795 = true := by quickRfl
theorem oK : Nat.beq (CFSG.KC.LQT.L.lenA CFSG.KD.LQT.M24Trio.B) 30 = true := by quickRfl
theorem ob0 : trB 0 = true := by quickRfl
theorem ob1 : trB 1 = true := by quickRfl
theorem ob2 : trB 2 = true := by quickRfl
theorem ob3 : trB 3 = true := by quickRfl

end CFSG.KD.LQT.C4094

end
