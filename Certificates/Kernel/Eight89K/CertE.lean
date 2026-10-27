module

public import Certificates.Kernel.Eight89K.Tree6
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 CFSG.KC.GRing

public section

#kc_repo #kc_json_gz CFSG.KD.E89E "Certificates/Kernel/Eight89K/data/B1491e.json.gz"
  298170 5998386920986529567 (ws : List (List Nat)) (S : Nat) (terms : List (List Nat × Nat))
  (vt : List (List Nat × (Nat × Bool))) (V : Nat) (gm : List (List Nat × (Nat × Bool)))

namespace CFSG.KC.Eight89K

theorem certE_tabs :
    tabsCheck 162 KData.m6aT.toList KData.m6bT.toList CFSG.KD.E89E.ws CFSG.KD.E89E.S
      CFSG.KD.E89E.terms = true := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem certE_v :
    vCheck 162 KData.m6aT.toList KData.m6bT.toList CFSG.KD.E89T6.bs CFSG.KD.E89E.vt
      CFSG.KD.E89E.V CFSG.KD.E89T6.tree = true := by
  decide +kernel

theorem certE_root :
    sumRoot 162 KData.m6aT.toList KData.m6bT.toList CFSG.KD.E89E.V CFSG.KD.E89E.terms
      CFSG.KD.E89E.gm CFSG.KD.E89T6.bs = true := by
  decide +kernel

@[expose] noncomputable def certEChunk (i : Nat) : Bool :=
  sumChunk 162 KData.m6aT.toList KData.m6bT.toList CFSG.KD.E89E.V CFSG.KD.E89E.terms
    CFSG.KD.E89E.gm CFSG.KD.E89T6.bs ((CFSG.KD.E89T6.tree.drop (216 * i)).take 216)

#kc_each CFSG.KC.Eight89K.certEChunk 0 10

end CFSG.KC.Eight89K

end
