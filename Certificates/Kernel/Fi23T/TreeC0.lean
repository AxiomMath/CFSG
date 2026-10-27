module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Fi23T CFSG.KD.Fi23K

theorem c0 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 0) (nat_lit 0)
    (nat_lit 1) = true := by quickRfl
theorem c1 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 1) (nat_lit 1)
    (nat_lit 4096) = true := by quickRfl
theorem c2 : trK G H (nat_lit 16) (nat_lit 42) (nat_lit 5) (domTc H) (nat_lit 1) (nat_lit 4097)
    (nat_lit 4096) = true := by quickRfl

end CFSG.KD.Fi23T

end
