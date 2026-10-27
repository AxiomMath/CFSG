module

public import Certificates.Data.Kernel.HNF26729K
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.HNF26729 "Certificates/Kernel/HNF26729/data/orb.json.gz" 3043 10967316824516539018
    (v : Nat) (tree : List (Nat × Nat)) (ord : List Nat)

public section

namespace CFSG.KD.HNF26729

noncomputable abbrev mul : Nat → Nat → Nat :=
  CFSG.KC.Ord.mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

noncomputable abbrev vec : Nat → Nat → Nat :=
  CFSG.KC.Ord.vecR 5 13 1729 133 9 CFSG.KD.FamHNSeed.LV CFSG.KD.FamHNSeed.HV CFSG.KD.FamHNSeed.RM

noncomputable abbrev vldV : Nat → Bool :=
  CFSG.KC.Ord.validM 5 1729 CFSG.KD.FamHNSeed.LV CFSG.KD.FamHNSeed.HV

@[expose] noncomputable def Bi : Nat := mul (CFSG.KD.FamHNSeed.RW 2) (CFSG.KD.FamHNSeed.RW 2)

@[expose] noncomputable def fullW (w1 w2 w8 u0 u1 : List Int) (v : Nat) (t : List (Nat × Nat))
    (o : List Nat) : Bool :=
  CFSG.KC.HNF26729.full mul vec vldV (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE w1 w2 w8 u0 u1 v 240 t o

end CFSG.KD.HNF26729

end
