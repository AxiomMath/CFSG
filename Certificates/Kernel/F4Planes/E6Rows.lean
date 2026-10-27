module

public import Certificates.Kernel.F4Planes.E6Pins
public import Certificates.Kernel.F4Planes.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4PlanesE6 "Certificates/Kernel/F4Planes/data/e6rows.json.gz"
  616701 5673021577970917268 (ij : List (Nat × Nat)) (gens : List (List (Nat × Nat × Nat × Nat)))
  (tgs : List (List (List Nat)))

#kc_each CFSG.KD.F4PlanesE6.ch14949rw r (fun r => CFSG.KC.F4PlanesE6.rowAt CFSG.KD.F4PlanesE6.LP
  CFSG.KD.F4PlanesE6.IP CFSG.KD.F4PlanesE6.IPi CFSG.KD.F4PlanesE6.pS6 CFSG.KD.F4Planes.PR
  CFSG.KD.F4PlanesE6.ij CFSG.KD.F4PlanesE6.gens CFSG.KD.F4PlanesE6.tgs r) 0 67

namespace CFSG.KD.F4PlanesE6

open CFSG.KC.F4PlanesE6

theorem neg_rw6_word : (!rowAt LP IP IPi pS6 CFSG.KD.F4Planes.PR ij
    (gens.map (List.map fun g => (Nat.add g.1 1, g.2))) tgs 0) = true := by
  quickRfl

theorem neg_rw6_tgt : (!rowAt LP IP IPi pS6 CFSG.KD.F4Planes.PR ij gens
    (tgs.map (List.map List.tail)) 0) = true := by
  quickRfl

theorem neg_rw6_shift : (!rowAt LP IP IPi pS6 CFSG.KD.F4Planes.PR (ij.drop 5) (gens.drop 5)
    (tgs.drop 5) 0) = true := by
  quickRfl

end CFSG.KD.F4PlanesE6

end
