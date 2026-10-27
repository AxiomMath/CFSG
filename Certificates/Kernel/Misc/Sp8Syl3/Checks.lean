module

public import Certificates.Data.Kernel.Misc.Sp8Syl3
public import Certificates.Kernel.Misc.Sp8Syl3.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp8Syl3

theorem sy3_tabE_ok : tabEK REC 81 = true := by quickRfl

theorem sy3_tabP_ok : tabPK REC 243 = true := by quickRfl

theorem sy3_e0_ok : e0K REC = true := by quickRfl

theorem sy3_cp_ok : cpK REC 81 = true := by quickRfl

theorem sy3_conj_ok : conjK REC = true := by quickRfl

end CFSG.KD.Sp8Syl3

end
