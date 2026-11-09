module

public import Certificates.Data.Kernel.HNFOrbK
public import Certificates.Kernel.HNF26729.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json CFSG.KD.HNFOrb.O1 "Certificates/Kernel/HNFOrb/data/orb1.json" 39839 16758841185829550330
    (u : Nat) (mv : List (List Nat)) (ks : List (List Nat)) (ord : List Nat)

#kc_repo #kc_json CFSG.KD.HNFOrb.O2 "Certificates/Kernel/HNFOrb/data/orb2.json" 62758 2255032066607603094
    (u : Nat) (mv : List (List Nat)) (ks : List (List Nat)) (ord : List Nat)

#kc_repo #kc_json CFSG.KD.HNFOrb.O3 "Certificates/Kernel/HNFOrb/data/orb3.json" 165680 11821112050065751774
    (u : Nat) (mv : List (List Nat)) (ks : List (List Nat)) (ord : List Nat)

public section

namespace CFSG.KD.HNFOrb

open CFSG.KD.HNF26729 in
@[expose] noncomputable def chunkW (w1 w2 wi : List Int) (u : Nat) (ms K : List Nat) : Bool :=
  CFSG.KC.HNFOrb.chunk mul vec vldV (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE w1 w2 wi u ms K

end CFSG.KD.HNFOrb

end
