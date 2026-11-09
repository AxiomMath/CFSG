module

public import Certificates.Kernel.Sporadic.Fi23Fu.Checks
public import Certificates.Kernel.Sporadic.Fi23Fu.RelSplit
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

#kc_each CFSG.KD.Fi23Fu.relC 12 13

namespace CFSG.KD.Fi23Fu

#kc_natval relC13_v := CFSG.KC.Ord.segProd RF (CFSG.KC.Ord.mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253) (nat_lit 8) CFSG.KD.BrFi23.L
    CFSG.KD.BrFi23.H CFSG.KD.BrFi23.CM CFSG.KD.BrFi23.RM)
    CFSG.KD.BrFi23.ONE (nat_lit 24) (nat_lit 0) (nat_lit 36)
  (CFSG.KC.Ord.nthRel relsF (nat_lit 13)) (nat_lit 0) CFSG.KD.BrFi23.ONE

theorem relC13_p1 : Nat.beq (CFSG.KC.Ord.segProd RF (CFSG.KC.Ord.mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253) (nat_lit 8) CFSG.KD.BrFi23.L
    CFSG.KD.BrFi23.H CFSG.KD.BrFi23.CM CFSG.KD.BrFi23.RM)
    CFSG.KD.BrFi23.ONE (nat_lit 24) (nat_lit 0) (nat_lit 36)
    (CFSG.KC.Ord.nthRel relsF (nat_lit 13)) (nat_lit 0) CFSG.KD.BrFi23.ONE) relC13_v = true := by
  quickRfl

theorem relC13_p2 : Nat.beq (CFSG.KC.Ord.segProd RF (CFSG.KC.Ord.mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253) (nat_lit 8) CFSG.KD.BrFi23.L
    CFSG.KD.BrFi23.H CFSG.KD.BrFi23.CM CFSG.KD.BrFi23.RM)
    CFSG.KD.BrFi23.ONE (nat_lit 24) (nat_lit 36)
    (CFSG.KC.Ord.lenL (CFSG.KC.Ord.nthRel relsF (nat_lit 13))) (CFSG.KC.Ord.nthRel relsF (nat_lit 13)) (nat_lit 0) relC13_v) CFSG.KD.BrFi23.ONE = true := by
  quickRfl

theorem relC13_hr : Nat.blt (nat_lit 13) (CFSG.KC.Ord.lenL relsF) = true := by
  quickRfl

theorem relC13_h0 : Nat.blt (nat_lit 0) (CFSG.KC.Ord.lenL (CFSG.KC.Ord.nthRel relsF (nat_lit 13))) = true := by
  quickRfl

theorem relC13_hm : Nat.ble (nat_lit 36) (CFSG.KC.Ord.lenL (CFSG.KC.Ord.nthRel relsF (nat_lit 13))) = true := by
  quickRfl

theorem relC13 : relC (nat_lit 13) = true :=
  relOK_split (nat_lit 36) relC13_v relC13_hr relC13_h0 relC13_hm relC13_p1 relC13_p2

end CFSG.KD.Fi23Fu

end
