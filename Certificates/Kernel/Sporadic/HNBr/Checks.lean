module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Kernel.Sporadic.HNBr.Data
public import CFSG.Certificates.Kernel.Orders.HN.Rels
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.BrHN "Certificates/Kernel/Sporadic/HNBr/data/hs.json.gz" 286
  8892547538306036476 (HS : List Nat)

public noncomputable section

namespace CFSG.KD.BrHN

theorem consts : CFSG.KC.Ord.constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true := by quickRfl

theorem hroots : CFSG.KC.Ord.rootsOK RH (CFSG.KC.Ord.validM 5 229957 L H) 1 6 = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RH (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM)
    (CFSG.KC.Ord.validM 5 229957 L H) 5 ONE = true := by
  quickRfl

theorem hAB : CFSG.KC.Ord.andB (CFSG.KC.Ord.regBelow 16 25) (CFSG.KC.Ord.regBelow 24 25) = true := by
  quickRfl

theorem hs : Nat.beq (CFSG.KC.Ord.runSlp RH (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM)
    (CFSG.KC.Ord.validM 5 229957 L H) ONE HS 6) 25 = true := by
  quickRfl

theorem relN : Nat.beq (CFSG.KC.Ord.lenRels CFSG.KD.OrdHN.rels) 19 = true := by quickRfl

theorem relB : CFSG.KC.Ord.relsBounded CFSG.KD.OrdHN.rels 5 = true := by quickRfl

@[expose] def relC (r : Nat) : Bool :=
  CFSG.KC.Ord.relOK RH (CFSG.KC.Ord.mulR 5 13 1729 133 9 L H CM RM) CFSG.KD.OrdHN.rels 5 ONE r

end CFSG.KD.BrHN

#kc_each CFSG.KD.BrHN.relC 0 19

namespace CFSG.KD.BrHN

#kc_forall_chunks R.all (fun r => relC r = true) 19 CFSG.KD.BrHN.relC 1

end CFSG.KD.BrHN

end
