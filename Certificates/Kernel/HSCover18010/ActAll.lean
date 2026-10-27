module

public import Certificates.Kernel.HSCover18010.ActData
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KHS18010

open CFSG.KC.MiscCoset.Act

theorem all : allR (nat_lit 0) (nat_lit 11200)
    (coverPointOK A B (nat_lit 3) (nat_lit 11200) R W) = true := by
  allR_blocks 16

theorem cyc0 : cycleOK A (Nat.add (nat_lit 3) (nat_lit 3)) C0 (nat_lit 2) = true := by
  quickRfl

end CFSG.KHS18010

end
