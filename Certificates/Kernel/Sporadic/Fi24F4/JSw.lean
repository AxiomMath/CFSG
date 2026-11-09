module

public import Certificates.Kernel.Sporadic.Fi24F4.JT
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24F4.Ck

open CFSG.KD.Fi24F4.JXs

theorem swc0 : CFSG.KD.Fi24F4.swc (nat_lit 0) = true := stage_cw (by quickRfl)

theorem swc1 : CFSG.KD.Fi24F4.swc (nat_lit 1) = true := stage_cw (by quickRfl)

theorem swc2 : CFSG.KD.Fi24F4.swc (nat_lit 2) = true := stage_cw (by quickRfl)

theorem swc3 : CFSG.KD.Fi24F4.swc (nat_lit 3) = true := stage_cw (by quickRfl)

theorem swc4 : CFSG.KD.Fi24F4.swc (nat_lit 4) = true := stage_cw (by quickRfl)

end CFSG.KD.Fi24F4.Ck

end
