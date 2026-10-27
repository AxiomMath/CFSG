module

public import Certificates.Kernel.Eight89K.Tree3
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 CFSG.KC.GRing

public section

#kc_repo #kc_json_gz CFSG.KD.E89D "Certificates/Kernel/Eight89K/data/B1491d.json.gz"
  76060 8736143000704561853 (ws : List (List Nat)) (S : Nat) (terms : List (List Nat × Nat))
  (vt : List (List Nat × (Nat × Bool))) (V : Nat) (gm : List (List Nat × (Nat × Bool)))

namespace CFSG.KC.Eight89K

theorem certD_tabs :
    tabsCheck 18 KData.m3aT.toList KData.m3bT.toList CFSG.KD.E89D.ws CFSG.KD.E89D.S
      CFSG.KD.E89D.terms = true := by
  decide +kernel

theorem certD_v :
    vCheck 18 KData.m3aT.toList KData.m3bT.toList CFSG.KD.E89T3.bs CFSG.KD.E89D.vt
      CFSG.KD.E89D.V CFSG.KD.E89T3.tree = true := by
  decide +kernel

theorem certD_root :
    sumRoot 18 KData.m3aT.toList KData.m3bT.toList CFSG.KD.E89D.V CFSG.KD.E89D.terms
      CFSG.KD.E89D.gm CFSG.KD.E89T3.bs = true := by
  decide +kernel

@[expose] noncomputable def certDChunk (i : Nat) : Bool :=
  sumChunk 18 KData.m3aT.toList KData.m3bT.toList CFSG.KD.E89D.V CFSG.KD.E89D.terms
    CFSG.KD.E89D.gm CFSG.KD.E89T3.bs ((CFSG.KD.E89T3.tree.drop (216 * i)).take 216)

#kc_each CFSG.KC.Eight89K.certDChunk 0 5

end CFSG.KC.Eight89K

end
