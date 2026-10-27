module

public import Certificates.Data.Eight89KModels
public import Certificates.Data.Kernel.GRing
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 CFSG.KC.GRing

public section

#kc_repo #kc_json_gz CFSG.KD.E89T3 "Certificates/Kernel/Eight89K/data/B1491t3.json.gz"
  14378 11236253824849630671 (bs : List Nat) (tree : List (List Nat × Nat))

namespace CFSG.KC.Eight89K

theorem tree3_ok :
    treeCheck 18 KData.m3aT.toList KData.m3bT.toList CFSG.KD.E89T3.bs CFSG.KD.E89T3.tree 1080 =
      true := by
  decide +kernel

end CFSG.KC.Eight89K

end
