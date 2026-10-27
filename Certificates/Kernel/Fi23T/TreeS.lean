module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Fi23T CFSG.KD.Fi23K

theorem a_tree : trK G H (nat_lit 8) (nat_lit 40) (nat_lit 10) (domT H) (nat_lit 0) (nat_lit 0)
    (nat_lit 3240) = true := by quickRfl
theorem a_cov : covK H (nat_lit 8) (nat_lit 3240) (domT H) = true := by quickRfl
theorem f_tree : trK G H (nat_lit 28) (nat_lit 41) (nat_lit 9) (domO H) (nat_lit 0) (nat_lit 0)
    (nat_lit 1080) = true := by quickRfl
theorem f_cov : covK H (nat_lit 28) (nat_lit 1080) (domO H) = true := by quickRfl
theorem g_tree : trK G H (nat_lit 32) (nat_lit 41) (nat_lit 9) (domR H) (nat_lit 0) (nat_lit 0)
    (nat_lit 2160) = true := by quickRfl
theorem g_cov : covK H (nat_lit 32) (nat_lit 2160) (domR H) = true := by quickRfl
theorem h_tree : ctK G H (nat_lit 36) (nat_lit 0) (nat_lit 1080) = true := by quickRfl
theorem h_cov : covK H (nat_lit 36) (nat_lit 1080) (domO H) = true := by quickRfl

end CFSG.KD.Fi23T

end
