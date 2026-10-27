module

public import Certificates.Data.Kernel.F4PlanesRow
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4Planes "Certificates/Kernel/F4Planes/data/pins.json.gz" 7284
  12852867051033098006 (gw : List Nat) (gl : List Nat) (paths : List (List Nat)) (pS : List Nat)

namespace CFSG.KD.F4Planes

open CFSG.KC.F4Planes

theorem pin_ok : pinP gw gl paths pS = true := by quickRfl

theorem rel_ok : relP pS = true := by quickRfl

theorem neg_pin : (!pinP gw gl paths (pS.map (Nat.add (Nat.shiftLeft 1 200)))) = true := by
  quickRfl

theorem neg_rel : (!relP [pS.getD 0 0, pS.getD 1 0, pS.getD 2 0, pS.getD 3 0, pS.getD 5 0,
    pS.getD 4 0]) = true := by
  quickRfl

end CFSG.KD.F4Planes

end
