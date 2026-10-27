module

public import Certificates.Data.Kernel.HN3K
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.HN3 "Certificates/Kernel/HN3/data/regs.items.gz" 172489 13928110532256865320
    regs[]
#kc_repo #kc_json_gz CFSG.KD.HN3 "Certificates/Kernel/HN3/data/hn3.json.gz" 412787 14033165728886441635
    (prog : List (List Nat)) (rels : List (List Nat))
    (g2 : List (List Nat)) (S2 : List Nat) (I2 : List (List Nat)) (T2 : List (Nat × Nat))
    (O2 : List Nat)
    (g3 : List (List Nat)) (S3 : List Nat) (I3 : List (List Nat)) (T3 : List (Nat × Nat))
    (O3 : List Nat)
    (g5 : List (List Nat)) (S5 : List Nat) (I5 : List (List Nat)) (T5 : List (Nat × Nat))
    (O5 : List Nat)

public section

namespace CFSG.KD.HN3

noncomputable abbrev mul : Nat → Nat → Nat :=
  CFSG.KC.Ord.mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

noncomputable abbrev vec : Nat → Nat → Nat :=
  CFSG.KC.Ord.vecR 5 13 1729 133 9 CFSG.KD.FamHNSeed.LV CFSG.KD.FamHNSeed.HV CFSG.KD.FamHNSeed.RM

noncomputable abbrev vldV : Nat → Bool :=
  CFSG.KC.Ord.validM 5 1729 CFSG.KD.FamHNSeed.LV CFSG.KD.FamHNSeed.HV

end CFSG.KD.HN3

end
