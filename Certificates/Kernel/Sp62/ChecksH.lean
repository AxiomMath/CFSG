module

public import Certificates.Data.Kernel.Sp62Pk
public import Certificates.Kernel.Sp62.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62

theorem hyp0_ok : hypK REC 14 38 2160 34 = true := by quickRfl
theorem hyp1_ok : hypK REC 15 38 2160 34 = true := by quickRfl
theorem hyp2_ok : hypK REC 16 38 2160 34 = true := by quickRfl
theorem hyp3_ok : hypK REC 17 38 2160 34 = true := by quickRfl
theorem hyp4_ok : hypK REC 18 2199 2160 34 = true := by quickRfl
theorem hyp5_ok : hypK REC 19 2199 2160 34 = true := by quickRfl
theorem hyp6_ok : hypK REC 20 2199 2160 34 = true := by quickRfl
theorem hyp7_ok : hypK REC 21 4360 2160 34 = true := by quickRfl
theorem hyp8_ok : hypK REC 22 6630 108 2 = true := by quickRfl
theorem hyp9_ok : hypK REC 23 6630 108 2 = true := by quickRfl
theorem hyp10_ok : hypK REC 24 4360 2160 34 = true := by quickRfl
theorem hyp11_ok : hypK REC 25 6521 108 2 = true := by quickRfl
theorem hyp12_ok : hypK REC 26 6521 108 2 = true := by quickRfl

end CFSG.KD.Sp62

end
