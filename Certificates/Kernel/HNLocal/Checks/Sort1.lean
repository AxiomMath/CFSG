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

theorem so1_0 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x85f) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so1_1 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0xa77) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so1_2 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0xc8f) (nat_lit 0x218) =
    true := by
  quickRfl

theorem so1_3 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0xea7) (nat_lit 0x217) =
    true := by
  quickRfl

theorem so1 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x85f) (nat_lit 0x85f) =
    true := by
  have h := sortRange_join (sortRange_join (sortRange_join so1_0 so1_1) so1_2) so1_3
  exact h

end CFSG.KD.HNLocal

end
