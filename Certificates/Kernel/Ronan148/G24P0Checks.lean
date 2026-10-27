module

public import Certificates.Data.Kernel.Misc.G24P0
public import Certificates.Kernel.Misc.G24Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Ronan148.G24P0

open CFSG.KC.Misc.G24 CFSG.KD.Misc.G24

@[expose] def p1C : List Nat :=
  [103, 100, 98, 103, 97, 98, 99, 100, 98, 99, 98, 101, 100, 99, 98, 103, 98, 97, 99, 100, 99, 98]

@[expose] def p2C : List Nat :=
  [103, 98, 103, 101, 97, 98, 97, 99, 100, 98, 99, 98, 97, 101, 100, 103, 98, 97, 99, 98, 97,
    100, 99, 98, 100, 103]

theorem kP0 : g24P0K Gb p1C p2C (nthL XS 5) (nthL YS 5) = true := by quickRfl

end CFSG.KD.Ronan148.G24P0

end
