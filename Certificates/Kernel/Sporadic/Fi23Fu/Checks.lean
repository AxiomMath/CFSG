module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.Fi23Fu.Data
public import Certificates.Kernel.Sporadic.Fi23Fu.Words
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.Fi23Fu

theorem hroots : CFSG.KC.Ord.rootsOK RF (CFSG.KC.Ord.validM (nat_lit 3) (nat_lit 704099)
    CFSG.KD.BrFi23.L CFSG.KD.BrFi23.H) (nat_lit 1) (nat_lit 25) = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RF (CFSG.KC.Ord.mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783)
    (nat_lit 253) (nat_lit 8) CFSG.KD.BrFi23.L CFSG.KD.BrFi23.H CFSG.KD.BrFi23.CM CFSG.KD.BrFi23.RM)
    (CFSG.KC.Ord.validM (nat_lit 3) (nat_lit 704099) CFSG.KD.BrFi23.L CFSG.KD.BrFi23.H) (nat_lit 24)
    CFSG.KD.BrFi23.ONE = true := by
  quickRfl

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels relsF) (nat_lit 14) = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded relsF (nat_lit 24) = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RF (CFSG.KC.Ord.mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253)
    (nat_lit 8) CFSG.KD.BrFi23.L CFSG.KD.BrFi23.H CFSG.KD.BrFi23.CM CFSG.KD.BrFi23.RM) relsF
    (nat_lit 24) CFSG.KD.BrFi23.ONE r

end CFSG.KD.Fi23Fu

end
