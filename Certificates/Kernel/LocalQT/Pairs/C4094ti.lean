module

public import Certificates.Kernel.LocalQT.Pairs.C4094h
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4094

open CFSG.KC.LQT.PH CFSG.KD.LQT.M24Chain CFSG.KD.LQT.M24Idx

@[expose] noncomputable def ti (k : Nat) : Bool := hkDBlk 24 CT0 (CT0.map (posReps 24)) I k

theorem tiN : Nat.beq (CFSG.KC.LQT.S.lenL I.flatten) 64512 = true := by quickRfl

end CFSG.KD.LQT.C4094

#kon_slices CFSG.KD.LQT.C4094.ti 0 8

end
