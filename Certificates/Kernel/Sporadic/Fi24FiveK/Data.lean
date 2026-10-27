module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24NetPt
public import Certificates.Data.Kernel.Spor.Fi24FiveK

#kc_repo #kc_json_gz CFSG.KD.Fi24FiveK.D "Certificates/Kernel/Sporadic/Fi24FiveK/data/five.json.gz"
  61613 9878709219629847279
  (M : List (List Nat)) (H : List Nat) (C : List (List Nat)) (R : List (List Nat))

public section

namespace CFSG.KD.Fi24FiveK

open CFSG.KC.Fi24FiveK CFSG.KC.Fi24Base CFSG.KC.Fi24NetPt

@[expose] noncomputable def E : List Nat → List Nat → Bool := eqB (letN CFSG.KD.Fi24Net.NW)

@[expose] noncomputable def letc (j : Nat) : Bool := letOK E D.M j

@[expose] noncomputable def stg (k : Nat) : Bool := stageOK E D.M D.C D.R k

@[expose] noncomputable def head : Bool := headOK E D.M D.H D.R 331

@[expose] noncomputable def bck : Bool := bOK E D.R

end CFSG.KD.Fi24FiveK

end
