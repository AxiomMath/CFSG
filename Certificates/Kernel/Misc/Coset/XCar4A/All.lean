module

public import Certificates.Kernel.Misc.Coset.XCar4A.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XCar4

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 720) (CFSG.KC.MiscCoset.Act.pointOK CFSG.KAct.XCar4.A (nat_lit 4) (nat_lit 720) CFSG.KAct.XCar4.rels) = true := by
  allR_blocks 32

theorem cyc0 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XCar4.A (Nat.add (nat_lit 4) (nat_lit 4)) [0, 2, 0, 2] (nat_lit 6) = true := by quickRfl

end CFSG.KAct.XCar4

end
