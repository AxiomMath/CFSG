module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Fi23Cov.Base
public import Certificates.Data.Kernel.Fi23Cov.Defs

#kc_repo #kc_json_gz CFSG.KD.Fi23Cov.F "Certificates/Kernel/Fi23Cov/data/five.json.gz" 16251
  11388357530733759919
  (U1 : List Nat) (U2 : List Nat) (H : List Nat) (M : List (List Nat)) (Ca : List (List Nat))
  (Ra : List (List Nat)) (Cb : List (List Nat)) (Rb : List (List Nat))

public section

namespace CFSG.KD.Fi23Cov

open CFSG.KC.Fi23Cov

@[expose] noncomputable def head : Bool := fHead E F.U1 F.U2 F.H F.M 28 F.Ra 51 F.Rb 36

@[expose] noncomputable def letc (j : Nat) : Bool := fLet E F.U1 F.U2 F.M j

@[expose] noncomputable def stA (k : Nat) : Bool := stOK E F.M F.Ca F.Ra k

@[expose] noncomputable def stB (k : Nat) : Bool := stOK E F.M F.Cb F.Rb k

@[expose] noncomputable def prA : Bool := prOK E F.Ra [39]

@[expose] noncomputable def prB : Bool := prOK E F.Rb [40]

end CFSG.KD.Fi23Cov

end
