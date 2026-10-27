module

public import Certificates.Kernel.Eight89K.Tree3
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 CFSG.KC.GRing

public section

#kc_repo #kc_json_gz CFSG.KD.E89C "Certificates/Kernel/Eight89K/data/B1491c.json.gz"
  55590 3449869382733193437 (ws : List (List Nat)) (S : Nat) (terms : List (List Nat))

namespace CFSG.KC.Eight89K

set_option maxRecDepth 20000 in
theorem certC_xor :
    xorCheck 18 KData.m3aT.toList KData.m3bT.toList CFSG.KD.E89C.ws CFSG.KD.E89C.S
      CFSG.KD.E89T3.bs CFSG.KD.E89C.terms = true := by
  decide +kernel

end CFSG.KC.Eight89K

end
