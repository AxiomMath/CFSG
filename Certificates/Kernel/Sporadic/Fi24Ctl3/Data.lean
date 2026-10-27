module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24NetPt
public import Certificates.Data.Kernel.Spor.Fi24Kn
public import Certificates.Data.Kernel.Spor.Fi24Ctl3

#kc_repo #kc_json_gz CFSG.KD.Fi24Ctl3.J "Certificates/Kernel/Sporadic/Fi24Ctl3/data/ctl3.json.gz" 1250
  17526088142069666151
  (R : List (List Nat)) (G : List (List Nat)) (X : List (List Nat)) (Y : List (List Nat))
  (H : List (List Nat))

public section

namespace CFSG.KD.Fi24Ctl3

open CFSG.KC.Fi24Kn CFSG.KC.Fi24NetPt CFSG.KC.Fi24Base CFSG.KC.Fi24Ctl3

@[expose] noncomputable def ck (i : Nat) : Bool :=
  ctlOK (eqB (letN CFSG.KD.Fi24Net.NW)) (nthW J.R i) (nthW J.G i) (nthW J.X i) (nthW J.Y i)
    (nthW J.H i)

end CFSG.KD.Fi24Ctl3

end
