module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.LyBr.Data
public import CFSG.Certificates.Kernel.Orders.Ly.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.BrLy

theorem consts : CFSG.KC.Ord.constsOK (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 111)
    (nat_lit 8) L H CM RM ONE LV HV = true := by
  quickRfl

theorem hroots : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H)
    (nat_lit 1) (nat_lit 7) = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12) (nat_lit 1332)
    (nat_lit 111) (nat_lit 8) L H CM RM) (CFSG.KC.Ord.validM (nat_lit 5) (nat_lit 147852) L H)
    (nat_lit 6) ONE = true := by
  quickRfl

theorem hAB : CFSG.KC.Ord.andB (CFSG.KC.Ord.regBelow (nat_lit 314) (nat_lit 3891))
    (CFSG.KC.Ord.regBelow (nat_lit 3890) (nat_lit 3891)) = true := by
  quickRfl

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels CFSG.KD.OrdLy.rels) (nat_lit 53) = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded CFSG.KD.OrdLy.rels (nat_lit 6) = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 111)
    (nat_lit 8) L H CM RM) CFSG.KD.OrdLy.rels (nat_lit 6) ONE r

end CFSG.KD.BrLy

#kc_each CFSG.KD.BrLy.relC 0 53

namespace CFSG.KD.BrLy

#kc_forall_chunks R.all (fun r => relC r = true) 53 CFSG.KD.BrLy.relC 1

end CFSG.KD.BrLy

end
