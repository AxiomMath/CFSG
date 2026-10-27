module

import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.ONOut.Data1

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.ONOut

theorem hroots : CFSG.KC.Ord.rootsOK RB VLD (nat_lit 1) (nat_lit 9) = true := by quickRfl

@[expose] def ivC (g : Nat) : Bool :=
  CFSG.KC.Ord.andB (VLD (RB (Nat.add (Nat.succ 8) g)))
    (Nat.beq (MUL (RB (Nat.succ g)) (RB (Nat.add (Nat.succ 8) g))) ONE)

@[expose] def sC (k : Nat) : Bool := CFSG.KC.Ord.progOK RB 8 RS MUL ONE (PS k) (RS k)

end CFSG.KD.ONOut

#kc_each CFSG.KD.ONOut.ivC 0 8

#kc_each CFSG.KD.ONOut.sC 0 16

end
