module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Fi23T CFSG.KD.Fi23K

theorem d0 : trK G H (nat_lit 20) (nat_lit 43) (nat_lit 5) (domTc H) (nat_lit 0) (nat_lit 0)
    (nat_lit 2916) = true := by quickRfl
theorem d1 : trK G H (nat_lit 20) (nat_lit 43) (nat_lit 5) (domTc H) (nat_lit 2916) (nat_lit 2916)
    (nat_lit 4096) = true := by quickRfl
theorem d2 : trK G H (nat_lit 20) (nat_lit 43) (nat_lit 5) (domTc H) (nat_lit 2916) (nat_lit 7012)
    (nat_lit 4096) = true := by quickRfl
theorem d3 : trK G H (nat_lit 20) (nat_lit 43) (nat_lit 5) (domTc H) (nat_lit 2916) (nat_lit 11108)
    (nat_lit 4096) = true := by quickRfl
theorem d4 : trK G H (nat_lit 20) (nat_lit 43) (nat_lit 5) (domTc H) (nat_lit 2916) (nat_lit 15204)
    (nat_lit 4096) = true := by quickRfl
theorem d5 : trK G H (nat_lit 20) (nat_lit 43) (nat_lit 5) (domTc H) (nat_lit 2916) (nat_lit 19300)
    (nat_lit 3299) = true := by quickRfl
theorem d6 : trK G H (nat_lit 20) (nat_lit 43) (nat_lit 5) (domTc H) (nat_lit 22599)
    (nat_lit 22599) (nat_lit 2916) = true := by quickRfl
theorem d7 : trK G H (nat_lit 20) (nat_lit 43) (nat_lit 5) (domTc H) (nat_lit 25515)
    (nat_lit 25515) (nat_lit 2916) = true := by quickRfl
theorem d_cov : covK H (nat_lit 20) (nat_lit 28431) (domTc H) = true := by quickRfl

end CFSG.KD.Fi23T

end
