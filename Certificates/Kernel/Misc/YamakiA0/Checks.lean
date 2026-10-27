module

public import Certificates.Data.Kernel.Misc.YamakiA0
public import Certificates.Kernel.Misc.YamakiA0.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.YamakiA0

theorem ya0_tab_ok : a0TabK REC 64 = true := by quickRfl

theorem ya0_gen_ok : a0GenK REC = true := by quickRfl

theorem ya0_hhat_ok : hhatK REC = true := by quickRfl

theorem ya0_four_ok : fourCheckK REC = true := by quickRfl

end CFSG.KD.YamakiA0

end
