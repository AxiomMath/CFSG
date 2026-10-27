module

public import Certificates.Data.Kernel.HNFDfsK
public import Certificates.Kernel.HNF26729.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

#kc_repo #kc_json_gz CFSG.KD.HNFO4 "Certificates/Kernel/HNFO4/data/o4.json.gz" 1208726 10292299440775741951
    (u : Nat) (codes : List (List (Nat × Nat × Nat))) (ord : List Nat)

public section

namespace CFSG.KD.HNFO4

open CFSG.KD.HNF26729

@[expose] def us : List (List Nat) := [[4], [5], [6], [], [4], [5], [6]]

@[expose] noncomputable def chkW (w1 w2 w4 : List Int) (i : Nat) : Bool :=
  CFSG.KC.HNFDfs.chunk mul vec vldV (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE w1 w2 w4 us u (CFSG.KC.HNFDfs.getC codes i)

@[expose] noncomputable def distW : Bool := CFSG.KC.HNFDfs.distK codes 69 ord 35200

end CFSG.KD.HNFO4

end
