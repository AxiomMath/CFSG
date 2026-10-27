module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24NetPt
public import Certificates.Data.Kernel.Spor.Fi24Kn
public import Certificates.Data.Kernel.Spor.Fi24PumpK

#kc_repo #kc_json_gz CFSG.KD.Fi24Pump.J "Certificates/Kernel/Sporadic/Fi24Pump/data/pump.json.gz" 587
  2593188081548988265
  (R : List (List Nat)) (V : List (List Nat)) (P : List Nat) (F : List Nat)

public section

namespace CFSG.KD.Fi24Pump

open CFSG.KC.Fi24Kn CFSG.KC.Fi24NetPt CFSG.KC.Fi24Base CFSG.KC.Fi24PumpK

@[expose] noncomputable def pck (i : Nat) : Bool :=
  pairOK (eqB (letN CFSG.KD.Fi24Net.NW)) (planeL CFSG.KD.Fi24Net.NW) (nthW J.R i) (nthW J.V i)
    (nthN J.P i) (nthN J.F i)

end CFSG.KD.Fi24Pump

end
