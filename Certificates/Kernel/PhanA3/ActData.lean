module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.Kernel.Bounds.LoadGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz

public section

#kc_repo #kc_blocked_gz CFSG.KAct.PhanA3.A "Certificates/Kernel/PhanA3/data/P3AAct.a.gz"
  8 4 65535 466560 6936417591408333506

namespace CFSG.KAct.PhanA3

@[expose] def R : List (List Nat) :=
  [[6, 6, 6], [0, 0, 0, 0], [0, 4, 1, 5], [0, 5, 3, 4, 3], [0, 6, 1, 6, 5], [2, 6, 3, 6, 2, 7],
   [10, 10, 10], [4, 4, 4, 4], [4, 8, 5, 9], [4, 9, 7, 8, 7], [4, 10, 5, 10, 9],
   [6, 10, 7, 10, 6, 11], [0, 8, 1, 9], [0, 10, 1, 11], [2, 8, 3, 9], [2, 10, 3, 11]]

#kc_repo #kc_json_gz CFSG.KAct.PhanA3 "Certificates/Kernel/PhanA3/data/P3AKW.json.gz" 2246
  4441161795123428167 (KW : List (List Nat))

@[expose] noncomputable def cycAll (A : Nat → Nat) (L : Nat) (us : List (List Nat)) (ℓ : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun u _ ih => CFSG.KC.MiscCoset.Act.andB (CFSG.KC.MiscCoset.Act.cycleOK A L u ℓ) ih) us

end CFSG.KAct.PhanA3

end
