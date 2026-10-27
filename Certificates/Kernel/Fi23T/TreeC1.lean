module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Fi23T CFSG.KD.Fi23K

theorem c3 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 1) (nat_lit 8193)
    (nat_lit 4096) = true := by quickRfl
theorem c4 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 1) (nat_lit 12289)
    (nat_lit 4096) = true := by quickRfl
theorem c5 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 1) (nat_lit 16385)
    (nat_lit 4096) = true := by quickRfl
theorem c6 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 1) (nat_lit 20481)
    (nat_lit 1920) = true := by quickRfl
theorem c7 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 22401)
    (nat_lit 22401) (nat_lit 3150) = true := by quickRfl
theorem c8 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 25551)
    (nat_lit 25551) (nat_lit 2880) = true := by quickRfl
theorem c_cov : covK H (nat_lit 16) (nat_lit 28431) (domTc H) = true := by quickRfl

end CFSG.KD.Fi23T

end
