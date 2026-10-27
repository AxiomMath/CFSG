module

public import Certificates.Data.Kernel.Misc.Sp6W
public import Certificates.Kernel.Misc.Sp6W.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp6W

theorem sp6w_z_ok : zRange D.Z 831 13 = true := by quickRfl

theorem sp6w_w0_ok : wRange D.N D.Z D.W 34146 831 0 4288 67 = true := by quickRfl

theorem sp6w_w1_ok : wRange D.N D.Z D.W 34146 831 4288 4288 67 = true := by quickRfl

theorem sp6w_w2_ok : wRange D.N D.Z D.W 34146 831 8576 4288 67 = true := by quickRfl

theorem sp6w_w3_ok : wRange D.N D.Z D.W 34146 831 12864 4288 67 = true := by quickRfl

theorem sp6w_w4_ok : wRange D.N D.Z D.W 34146 831 17152 4288 67 = true := by quickRfl

theorem sp6w_w5_ok : wRange D.N D.Z D.W 34146 831 21440 4288 67 = true := by quickRfl

theorem sp6w_w6_ok : wRange D.N D.Z D.W 34146 831 25728 4288 67 = true := by quickRfl

theorem sp6w_w7_ok : wRange D.N D.Z D.W 34146 831 30016 4130 65 = true := by quickRfl

end CFSG.KD.Sp6W

end
