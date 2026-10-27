module

public import Certificates.Kernel.F4Planes.Pins
public import Certificates.Kernel.F4Planes.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4Planes "Certificates/Kernel/F4Planes/data/rows.json.gz" 499190
  8694890198642737951 (gens : List (List (Nat × Nat × Nat × Nat × Nat × Nat)))
  (tgs : List (List (List Nat)))

#kc_each CFSG.KD.F4Planes.ch14950rw r (fun r => CFSG.KC.F4Planes.rowP CFSG.KD.F4Planes.pS
  CFSG.KD.F4Planes.PR CFSG.KD.F4Planes.gens CFSG.KD.F4Planes.tgs r) 0 67

namespace CFSG.KD.F4Planes

open CFSG.KC.F4Planes

theorem neg_rw_word : (!rowP pS PR (gens.map (List.map fun g => (Nat.add g.1 1, g.2))) tgs 0) =
    true := by
  quickRfl

theorem neg_rw_tgt : (!rowP pS PR gens (tgs.map (List.map List.tail)) 0) = true := by
  quickRfl

theorem neg_rw_shift : (!rowP pS PR gens.tail tgs.tail 0) = true := by
  quickRfl

end CFSG.KD.F4Planes

end
