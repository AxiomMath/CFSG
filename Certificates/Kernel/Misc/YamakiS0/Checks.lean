module

public import Certificates.Data.Kernel.Misc.YamakiS0
public import Certificates.Kernel.Misc.YamakiS0.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.YamakiS0

open CFSG.KD.Sp62

theorem ys0_tab_ok : s0TabK REC 512 = true := by quickRfl

theorem ys0_sq1_ok : s0SqK REC ONE 144 = true := by quickRfl

theorem ys0_sqa_ok : s0SqK REC (REC 5) 0 = true := by quickRfl

theorem ys0_sqb_ok : s0SqK REC (REC 4) 48 = true := by quickRfl

theorem ys0_sqc_ok : s0SqK REC (MULF (REC 5) (REC 4)) 32 = true := by quickRfl

theorem ys0_comma_ok : s0CommK REC (REC 5) = true := by quickRfl

theorem ys0_commb_ok : s0CommK REC (REC 4) = true := by quickRfl

theorem ys0_cent_ok : s0CentK REC (REC 5) (REC 4) = true := by quickRfl

end CFSG.KD.YamakiS0

end
