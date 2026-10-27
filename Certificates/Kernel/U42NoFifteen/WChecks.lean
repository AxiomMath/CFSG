module

public import Certificates.Kernel.U42NoFifteen.WData
public import Certificates.Data.Kernel.ConjWalk
public import Certificates.Data.Kernel.ConjCountL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface

set_option maxRecDepth 100000

public section

namespace CFSG.KD.U42NF

open CFSG.KC.ConjWalk CFSG.KC.ConjCount CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.QuasithinUnique.K1.SporadicPerm

theorem ch26122w : walkK 45 0 1 3 (encL 64 (t.getD 0 [])) (encL 64 (ti.getD 0 []))
    (encL 64 (t.getD 1 [])) (encL 64 (ti.getD 1 [])) (encL 64 (t.getD 1 [])) recs = true := by
  quickRfl

theorem ch26122w_len : recs.length = 1739 := by decide +kernel

theorem ch26122w_tabs : (t == [x45, y45].map (tab 45)) = true := by decide +kernel

theorem ch26122w_inv :
    (invOK 45 (t.getD 0 []) (ti.getD 0 []) && invOK 45 (t.getD 1 []) (ti.getD 1 [])) = true := by
  decide +kernel

theorem ch26122w_ord :
    (tabW t 45 [1, 1, 1, 1, 1] == List.range 45 && !(tabW t 45 [1] == List.range 45)) = true := by
  decide +kernel

end CFSG.KD.U42NF

end
