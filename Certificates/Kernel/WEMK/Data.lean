module

public import Certificates.Data.Kernel.WEMK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

open Certificates.WEMK in
#kc_repo #kc_json_gz CFSG.KD.WEMK.N4 "Certificates/Kernel/WEMK/data/n4.json.gz" 2863 8339006210748242271
  (S : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat)) (wd : List (List Nat))
  (x0 : Nat) (t0 : Nat) (tr : List (Nat × Nat)) (ord : List Nat) (cov : List Nat)

open Certificates.WEMK in
#kc_repo #kc_json_gz CFSG.KD.WEMK.EN4 "Certificates/Kernel/WEMK/data/en4.json.gz" 4164 16894610336457759742
  (S : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat)) (wd : List (List Nat))
  (x0 : Nat) (t0 : Nat) (tr : List (Nat × Nat)) (ord : List Nat) (cov : List Nat)

open Certificates.WEMK in
#kc_repo #kc_json_gz CFSG.KD.WEMK.K5 "Certificates/Kernel/WEMK/data/k5.json.gz" 4009 13919768262459098112
  (S : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat)) (wd : List (List Nat))
  (x0 : Nat) (t0 : Nat) (tr : List (Nat × Nat)) (ord : List Nat) (cov : List Nat)

open Certificates.WEMK in
#kc_repo #kc_json_gz CFSG.KD.WEMK.K6 "Certificates/Kernel/WEMK/data/k6.json.gz" 10370 7106111143159164884
  (S : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat)) (wd : List (List Nat))
  (x0 : Nat) (t0 : Nat) (tr : List (Nat × Nat)) (ord : List Nat) (cov : List Nat)

end
