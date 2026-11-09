module

public import Certificates.Kernel.HNLocal.XData
public import Certificates.Kernel.HNLocal.SortData
public import Certificates.Kernel.HNLocal.Data
public import Certificates.Kernel.HNLocal.Checks.Split
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.HNLocal

theorem so3_0 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x191d) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so3_1 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x1b35) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so3_2 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x1d4d) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so3_3 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x1f65) (nat_lit 0x217) =
    true := by
  quickRfl

theorem so3 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x191d) (nat_lit 0x85f) =
    true := by
  have h := sortRange_join (sortRange_join (sortRange_join so3_0 so3_1) so3_2) so3_3
  exact h

end CFSG.KD.HNLocal

end
