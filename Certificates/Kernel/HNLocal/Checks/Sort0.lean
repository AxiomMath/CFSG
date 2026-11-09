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

theorem so0_0 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x0) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so0_1 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x218) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so0_2 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x430) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so0_3 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x648) (nat_lit 0x217) =
    true := by
  quickRfl

theorem so0 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x0) (nat_lit 0x85f) =
    true := by
  have h := sortRange_join (sortRange_join (sortRange_join so0_0 so0_1) so0_2) so0_3
  exact h

end CFSG.KD.HNLocal

end
