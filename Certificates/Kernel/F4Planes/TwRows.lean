module

public import Certificates.Data.Kernel.F4PlanesTw
public import Certificates.Kernel.F4Planes.E6Pins
public import Certificates.Kernel.F4Planes.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4PlanesTw "Certificates/Kernel/F4Planes/data/tw.json.gz"
  272441 15854018672204135071 (X8 : Nat) (X9 : Nat) (ij : List (Nat × Nat))
  (gens : List (List (Nat × Nat × Nat))) (zs : List (List (List Nat)))

#kc_each CFSG.KD.F4PlanesTw.ch14946tw r (fun r => CFSG.KC.F4PlanesTw.rowAtT CFSG.KD.F4PlanesE6.IP
  CFSG.KD.F4PlanesTw.X8 CFSG.KD.F4PlanesTw.X9 CFSG.KD.F4PlanesE6.pS6 CFSG.KD.F4Planes.PR
  CFSG.KD.F4PlanesTw.ij CFSG.KD.F4PlanesTw.gens CFSG.KD.F4PlanesTw.zs r) 0 67

namespace CFSG.KD.F4PlanesTw

open CFSG.KC.F4PlanesTw

theorem neg_tw_word : (!rowAtT CFSG.KD.F4PlanesE6.IP X8 X9 CFSG.KD.F4PlanesE6.pS6
    CFSG.KD.F4Planes.PR ij (gens.map (List.map fun g => (Nat.add g.1 1, g.2))) zs 0) = true := by
  quickRfl

theorem neg_tw_tok : (!rowAtT CFSG.KD.F4PlanesE6.IP X8 X9 CFSG.KD.F4PlanesE6.pS6
    CFSG.KD.F4Planes.PR ij gens (zs.map (List.map List.tail)) 0) = true := by
  quickRfl

theorem neg_tw_shift : (!rowAtT CFSG.KD.F4PlanesE6.IP X8 X9 CFSG.KD.F4PlanesE6.pS6
    CFSG.KD.F4Planes.PR (ij.drop 5) (gens.drop 5) (zs.drop 5) 0) = true := by
  quickRfl

end CFSG.KD.F4PlanesTw

end
