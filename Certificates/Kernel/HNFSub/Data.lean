module

public import Certificates.Data.Kernel.HNFSubK
public import Certificates.Kernel.HNF26729.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.HNFSub.S7 "Certificates/Kernel/HNFSub/data/sub7.json.gz" 9388571 9468747812569078895
    (r0 : List Nat) (cols : List (List Nat)) (segs : List (List (List Nat))) (xm : Nat) (ym : Nat)

#kc_repo #kc_json_gz CFSG.KD.HNFSub.F7 "Certificates/Kernel/HNFSub/data/fib7.json.gz" 721 1313185370496110079
    (us : List (List Nat)) (ts : List (List Nat)) (u : Nat) (tree : List (Nat × Nat)) (ord : List Nat)

public section

namespace CFSG.KD.HNFSub

open CFSG.KD.HNF26729

@[expose] noncomputable def segW (w1 w2 : List Int) (c : Nat) : Bool :=
  CFSG.KC.HNFSub.segOK mul vec vldV (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE w1 w2 S7.r0 S7.cols (CFSG.KC.HNFSub.getSg S7.segs c)

@[expose] noncomputable def baseW (w : List Int) (j : Nat) : Bool :=
  CFSG.KC.HNFSub.baseOK mul vec (CFSG.KC.Ord.validM 5 229957 CFSG.KD.FamHNSeed.L
    CFSG.KD.FamHNSeed.H) vldV CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (CFSG.KD.FamHNSeed.RW 1)
    (CFSG.KD.FamHNSeed.RW 2) Bi CFSG.KD.FamHNSeed.ONE w S7.r0
    (CFSG.KC.HNFSub.getLs S7.cols j) S7.xm S7.ym

@[expose] noncomputable def fibW (w1 w2 w : List Int) (N : Nat) : Bool :=
  CFSG.KC.HNFSub.fibU mul vec vldV (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE w1 w2 w S7.r0 F7.us F7.ts F7.u N F7.tree F7.ord

end CFSG.KD.HNFSub

end
