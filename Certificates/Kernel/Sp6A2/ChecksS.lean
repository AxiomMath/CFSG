module

public import Certificates.Data.Kernel.Sp6A2K
public import Certificates.Kernel.Sp6A2.Rec
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6A2

theorem scanO0_799751 : scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 29 23 0 63 1 = true := by
  quickRfl
theorem scanO1_799751 : scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 93 86 0 315 5 = true := by
  quickRfl
theorem scanO2a_799751 : scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 409 401 0 512 8 = true := by
  quickRfl
theorem scanO2b_799751 : scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 409 401 512 433 7 = true := by
  quickRfl

end CFSG.KD.Sp6A2

end
