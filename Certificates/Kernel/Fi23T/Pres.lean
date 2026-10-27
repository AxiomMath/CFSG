module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Fi23T CFSG.KD.Fi23K

theorem q_0 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 0] = true := by quickRfl
theorem q_1 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 1] = true := by quickRfl
theorem q_32 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 32] = true := by quickRfl
theorem q_37 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 37] = true := by quickRfl
theorem q_39 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 39] = true := by quickRfl
theorem q_49 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 49] = true := by quickRfl
theorem q_52 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 52] = true := by quickRfl
theorem q_53 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 53] = true := by quickRfl
theorem q_59 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 59] = true := by quickRfl
theorem q_64 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 64] = true := by quickRfl
theorem q_71 : presK G H (nat_lit 0) (nat_lit 3240) [nat_lit 71] = true := by quickRfl

theorem o_1 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 1] = true := by quickRfl
theorem o_32 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 32] = true := by quickRfl
theorem o_37 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 37] = true := by quickRfl
theorem o_39 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 39] = true := by quickRfl
theorem o_49 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 49] = true := by quickRfl
theorem o_52 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 52] = true := by quickRfl
theorem o_53 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 53] = true := by quickRfl
theorem o_59 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 59] = true := by quickRfl
theorem o_64 : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 64] = true := by quickRfl

theorem cs_ok : presK G H (nat_lit 2) (nat_lit 1080) [nat_lit 92, nat_lit 71] = true := by quickRfl

end CFSG.KD.Fi23T

end
