module

public import Certificates.Data.Eight89KModels
public import Certificates.Data.Kernel.GRing
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 CFSG.KC.GRing

public section

#kc_repo #kc_json_gz CFSG.KD.E89T6 "Certificates/Kernel/Eight89K/data/B1491t6.json.gz"
  25617 13552345691577245084 (bs : List Nat) (tree : List (List Nat × Nat))

namespace CFSG.KC.Eight89K

theorem tree6_ok :
    treeCheck 162 KData.m6aT.toList KData.m6bT.toList CFSG.KD.E89T6.bs CFSG.KD.E89T6.tree 2160 =
      true := by
  decide +kernel

end CFSG.KC.Eight89K

end
