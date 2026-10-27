module

public import Certificates.Kernel.HNLocal.ZData
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocalZ

theorem roots : CFSG.KC.Ord.rootsOK RZ CFSG.KD.HNLocal.vld (nat_lit 1) (nat_lit 87) = true := by
  quickRfl

theorem invs : CFSG.KC.Ord.invsOK RZ CFSG.KD.HNLocal.mul CFSG.KD.HNLocal.vld (nat_lit 86)
    CFSG.KD.OrdHN.ONE = true := by
  quickRfl

@[expose] noncomputable def pcTie (k : Nat) : Bool :=
  Nat.beq (RZ (Nat.add (nat_lit 64) k)) (CFSG.KD.HNLocal.PC k)

#kc_each CFSG.KD.HNLocalZ.pcTie 0 14

theorem ra : Nat.beq (RZ (nat_lit 1)) (CFSG.KD.OrdHN.RW (nat_lit 1)) = true := by quickRfl

theorem rb : Nat.beq (RZ (nat_lit 2)) (CFSG.KD.OrdHN.RW (nat_lit 2)) = true := by quickRfl

end CFSG.KD.HNLocalZ

end
