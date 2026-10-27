module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.Fi23Br.Data
public import Certificates.Kernel.Sporadic.Fi23Br.Words
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.BrFi23

theorem consts : CFSG.KC.Ord.constsOK (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253)
    (nat_lit 8) L H CM RM ONE LV HV = true := by
  quickRfl

theorem hroots : CFSG.KC.Ord.rootsOK RB (CFSG.KC.Ord.validM (nat_lit 3) (nat_lit 704099) L H)
    (nat_lit 1) (nat_lit 13) = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RB (CFSG.KC.Ord.mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783)
    (nat_lit 253) (nat_lit 8) L H CM RM) (CFSG.KC.Ord.validM (nat_lit 3) (nat_lit 704099) L H)
    (nat_lit 12) ONE = true := by
  quickRfl

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels relsX) (nat_lit 69) = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded relsX (nat_lit 12) = true := by quickRfl

end CFSG.KD.BrFi23

end
