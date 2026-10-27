module

public import Certificates.Data.Kernel.HNFFibK
public import Certificates.Kernel.HNF26729.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.HNFFib.F5 "Certificates/Kernel/HNFFib/data/fib5.json.gz" 1227 15449801581667020623
    (c : List Nat) (us : List (List Nat)) (u : Nat) (tree : List (Nat × Nat)) (ord : List Nat)

#kc_repo #kc_json_gz CFSG.KD.HNFFib.F6 "Certificates/Kernel/HNFFib/data/fib6.json.gz" 1106 3371602499378435221
    (c : List Nat) (us : List (List Nat)) (u : Nat) (tree : List (Nat × Nat)) (ord : List Nat)

#kc_repo #kc_json_gz CFSG.KD.HNFFib.F8 "Certificates/Kernel/HNFFib/data/fib8.json.gz" 813 15661280397906918845
    (c : List Nat) (us : List (List Nat)) (u : Nat) (tree : List (Nat × Nat)) (ord : List Nat)

public section

namespace CFSG.KD.HNFFib

open CFSG.KD.HNF26729 in
@[expose] noncomputable def fibW (w1 w2 wi wj : List Int) (c : List Nat) (us : List (List Nat))
    (u N : Nat) (t : List (Nat × Nat)) (o : List Nat) : Bool :=
  CFSG.KC.HNFFib.fib mul vec vldV (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE w1 w2 wi wj c us u N t o

end CFSG.KD.HNFFib

end
