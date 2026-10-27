module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Fi23T CFSG.KD.Fi23K

theorem e0 : trK G H (nat_lit 24) (nat_lit 43) (nat_lit 5) (domW G H [nat_lit 5, nat_lit 2])
    (nat_lit 0) (nat_lit 0) (nat_lit 2916) = true := by quickRfl
theorem e1 : trK G H (nat_lit 24) (nat_lit 43) (nat_lit 5) (domW G H [nat_lit 5, nat_lit 2])
    (nat_lit 2916) (nat_lit 2916) (nat_lit 2916) = true := by quickRfl
theorem e2 : trK G H (nat_lit 24) (nat_lit 43) (nat_lit 5) (domW G H [nat_lit 5, nat_lit 2])
    (nat_lit 5832) (nat_lit 5832) (nat_lit 4096) = true := by quickRfl
theorem e3 : trK G H (nat_lit 24) (nat_lit 43) (nat_lit 5) (domW G H [nat_lit 5, nat_lit 2])
    (nat_lit 5832) (nat_lit 9928) (nat_lit 4096) = true := by quickRfl
theorem e4 : trK G H (nat_lit 24) (nat_lit 43) (nat_lit 5) (domW G H [nat_lit 5, nat_lit 2])
    (nat_lit 5832) (nat_lit 14024) (nat_lit 4096) = true := by quickRfl
theorem e5 : trK G H (nat_lit 24) (nat_lit 43) (nat_lit 5) (domW G H [nat_lit 5, nat_lit 2])
    (nat_lit 5832) (nat_lit 18120) (nat_lit 4096) = true := by quickRfl
theorem e6 : trK G H (nat_lit 24) (nat_lit 43) (nat_lit 5) (domW G H [nat_lit 5, nat_lit 2])
    (nat_lit 5832) (nat_lit 22216) (nat_lit 3299) = true := by quickRfl
theorem e7 : trK G H (nat_lit 24) (nat_lit 43) (nat_lit 5) (domW G H [nat_lit 5, nat_lit 2])
    (nat_lit 25515) (nat_lit 25515) (nat_lit 2916) = true := by quickRfl
theorem e_cov : covK H (nat_lit 24) (nat_lit 28431) (domW G H [nat_lit 5, nat_lit 2]) = true := by
  quickRfl

end CFSG.KD.Fi23T

end
