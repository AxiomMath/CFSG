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

theorem so2_0 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x10be) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so2_1 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x12d6) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so2_2 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x14ee) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so2_3 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x1706) (nat_lit 0x217) =
    true := by
  quickRfl

theorem so2 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x10be) (nat_lit 0x85f) =
    true := by
  have h := sortRange_join (sortRange_join (sortRange_join so2_0 so2_1) so2_2) so2_3
  exact h

end CFSG.KD.HNLocal

end
