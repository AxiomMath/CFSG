module

public import Certificates.Kernel.Misc.Coset.XCar3A.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XCar3

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 120) (CFSG.KC.MiscCoset.Act.pointOK CFSG.KAct.XCar3.A (nat_lit 3) (nat_lit 120) CFSG.KAct.XCar3.rels) = true := by
  allR_blocks 60

theorem cyc0 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XCar3.A (Nat.add (nat_lit 3) (nat_lit 3)) [0, 2, 0, 2] (nat_lit 2) = true := by quickRfl

end CFSG.KAct.XCar3

end
