module

public import Certificates.Data.Kernel.HSMK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.WEMK in
#kc_repo #kc_json CFSG.KD.HSMK.K5 "Certificates/Kernel/HSMK/data/k5.json" 6492 109685414298206345
  (T : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat)) (cov : List Nat)
  (sidx : List Nat) (lv : List (List Nat × (List (List Nat × List Nat) × List KPair)))

open Certificates.WEMK in
#kc_repo #kc_json CFSG.KD.HSMK.K6 "Certificates/Kernel/HSMK/data/k6.json" 26298 16659455855058832146
  (T : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat)) (cov : List Nat)
  (sidx : List Nat) (R : List (List Nat × List Nat))

end
