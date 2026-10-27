module

public import Certificates.Kernel.PhanD4Dce.CTData
public import Certificates.Data.Kernel.Misc.Coset.ActOrbit
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz

set_option maxRecDepth 100000

#kc_repo #kc_json_gz CFSG.KAct.PhanD4Chain "Certificates/Kernel/PhanD4Dce/data/D4Chain.json.gz"
  12635 10213036681829461284 (LV : List (Nat × List Nat × List Nat))

public section

namespace CFSG.KAct.PhanD4CT

open CFSG.KC.MiscCoset.Act

theorem levels : levelsOK CFSG.KAct.PhanD4CT.A (nat_lit 58) (nat_lit 1120) CFSG.KAct.PhanD4Chain.LV
    [] = true := by
  decide +kernel

theorem ch270006_chain_fix : notB (levelsOK CFSG.KAct.PhanD4CT.A (nat_lit 58) (nat_lit 1120)
    [(0, [0], [])] [16]) = true := by quickRfl

theorem ch270006_chain_dup : notB (recOK CFSG.KAct.PhanD4CT.A (nat_lit 58) (nat_lit 1120) [0]
    [928, 928] (nat_lit 65536)) = true := by quickRfl

theorem ch270006_chain_parent : notB (recOK CFSG.KAct.PhanD4CT.A (nat_lit 58) (nat_lit 1120) [0]
    [58] (nat_lit 65536)) = true := by quickRfl

end CFSG.KAct.PhanD4CT

end
