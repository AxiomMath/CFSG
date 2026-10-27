module

public import Certificates.Data.Kernel.Misc.Sp8N0
public import Certificates.Kernel.Misc.Sp8N0.Rec
public import Certificates.Kernel.Misc.Sp8Syl3.Rec
public import Certificates.Data.RudvalisFF81Sp8Norm
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp8N0

set_option maxRecDepth 100000 in
theorem n04_tab_ok : n0TabK REC 31104 = true := by quickRfl

theorem n04_mem_ok : n0MemK REC = true := by quickRfl

theorem n04_conj_ok : n0ConjK REC CFSG.KD.Sp8Syl3.REC = true := by quickRfl

theorem n04_cls_ok : clsK REC CFSG.KD.Sp8Syl3.REC = true := by quickRfl

theorem n04_prod_ok : prodK REC = true := by quickRfl

theorem n04_norm_ok : normK REC = true := by quickRfl

theorem n04_fix_ok : CFSG.RankThree.PartTwo.Sec21.FF81.Sp8.fixChk899104 = true := by
  decide +kernel

end CFSG.KD.Sp8N0

end
