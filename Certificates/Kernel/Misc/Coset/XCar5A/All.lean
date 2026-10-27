module

public import Certificates.Kernel.Misc.Coset.XCar5A.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XCar5

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 2160) (CFSG.KC.MiscCoset.Act.pointOK CFSG.KAct.XCar5.A (nat_lit 5) (nat_lit 2160) CFSG.KAct.XCar5.rels) = true := by
  allR_blocks 16

theorem cyc0 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XCar5.A (Nat.add (nat_lit 5) (nat_lit 5)) [0, 2, 0, 2] (nat_lit 6) = true := by quickRfl

end CFSG.KAct.XCar5

end
