module

public import Certificates.Data.Kernel.F4PlanesE6
public import Certificates.Kernel.F4Planes.Pins
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4PlanesE6 "Certificates/Kernel/F4Planes/data/e6pins.json.gz"
  72990 12935241627660094178 (LP : Nat) (iw : List Nat) (il : List Nat) (IP : Nat) (IPi : Nat)
  (pS6 : List Nat)

namespace CFSG.KD.F4PlanesE6

open CFSG.KC.E6Salt CFSG.KC.F4PlanesE6

theorem let_ok : letOK LP = true := by quickRfl

theorem iota_ok : iotaB LP IP IPi iw il = true := by quickRfl

theorem pin6_ok : pinE IP CFSG.KD.F4Planes.gw CFSG.KD.F4Planes.gl CFSG.KD.F4Planes.paths pS6 =
    true := by
  quickRfl

theorem neg_let : (!letOK (Nat.xor LP (2 ^ 200))) = true := by quickRfl

theorem neg_iota : (!iotaB LP IP IPi (iw.map (Nat.add 1)) il) = true := by quickRfl

theorem neg_pin6 : (!pinE IP CFSG.KD.F4Planes.gw CFSG.KD.F4Planes.gl CFSG.KD.F4Planes.paths
    pS6.reverse) = true := by
  quickRfl

end CFSG.KD.F4PlanesE6

end
