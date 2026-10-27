module

public import Certificates.Data.Kernel.Misc.Sp6Over
public import Certificates.Kernel.Misc.Sp6Over.Rec
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Sp6Over

theorem ov_h6_ok : h6K REC = true := by quickRfl

theorem ov_pin_ok : pinK REC = true := by quickRfl

theorem ov_k_ok : kK REC 63 = true := by quickRfl

theorem ov_u_ok : uK REC = true := by quickRfl

theorem ov_form_ok : formK REC FL (packL [0, 1, 316, 3196, 6076, 9856, 13888]) = true := by
  quickRfl

end CFSG.KD.Sp6Over

end
