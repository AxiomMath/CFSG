module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Fi23T CFSG.KD.Fi23K

theorem b0 : trK G H (nat_lit 12) (nat_lit 41) (nat_lit 9) (domTc H) (nat_lit 0) (nat_lit 0)
    (nat_lit 4096) = true := by quickRfl
theorem b1 : trK G H (nat_lit 12) (nat_lit 41) (nat_lit 9) (domTc H) (nat_lit 0) (nat_lit 4096)
    (nat_lit 4096) = true := by quickRfl
theorem b2 : trK G H (nat_lit 12) (nat_lit 41) (nat_lit 9) (domTc H) (nat_lit 0) (nat_lit 8192)
    (nat_lit 4096) = true := by quickRfl
theorem b3 : trK G H (nat_lit 12) (nat_lit 41) (nat_lit 9) (domTc H) (nat_lit 0) (nat_lit 12288)
    (nat_lit 4096) = true := by quickRfl
theorem b4 : trK G H (nat_lit 12) (nat_lit 41) (nat_lit 9) (domTc H) (nat_lit 0) (nat_lit 16384)
    (nat_lit 4096) = true := by quickRfl
theorem b5 : trK G H (nat_lit 12) (nat_lit 41) (nat_lit 9) (domTc H) (nat_lit 0) (nat_lit 20480)
    (nat_lit 4096) = true := by quickRfl
theorem b6 : trK G H (nat_lit 12) (nat_lit 41) (nat_lit 9) (domTc H) (nat_lit 0) (nat_lit 24576)
    (nat_lit 3855) = true := by quickRfl
theorem b_cov : covK H (nat_lit 12) (nat_lit 28431) (domTc H) = true := by quickRfl

end CFSG.KD.Fi23T

end
