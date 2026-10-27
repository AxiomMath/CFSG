module

public import Certificates.Data.Kernel.Sp6A2K
public import Certificates.Kernel.Sp6A2.Rec
public import Certificates.Kernel.Sp6Two.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6A2

theorem scanO3a_799751 : scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 1355 1346 0 512 8 = true := by
  quickRfl
theorem scanO3b_799751 :
    scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 1355 1346 512 512 8 = true := by quickRfl
theorem scanO3c_799751 :
    scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 1355 1346 1024 512 8 = true := by quickRfl
theorem scanO3d_799751 :
    scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 1355 1346 1536 512 8 = true := by quickRfl
theorem scanO3e_799751 :
    scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 1355 1346 2048 512 8 = true := by quickRfl
theorem scanO3f_799751 :
    scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 1355 1346 2560 512 8 = true := by quickRfl
theorem scanO3g_799751 :
    scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 1355 1346 3072 512 8 = true := by quickRfl
theorem scanO3h_799751 :
    scanK CFSG.KD.Sp6Two.REC REC 17324581188 20 1355 1346 3584 196 4 = true := by quickRfl

end CFSG.KD.Sp6A2

end
