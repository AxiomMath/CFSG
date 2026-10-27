module

public import Certificates.Kernel.Misc.Coset.XSz8HA.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XSz8H

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 16640) (CFSG.KC.MiscCoset.Act.coverPointOK CFSG.KAct.XSz8H.A CFSG.KAct.XSz8H.B (nat_lit 2) (nat_lit 16640) CFSG.KAct.XSz8H.R CFSG.KAct.XSz8H.W) = true := by
  allR_blocks 16

theorem cyc0 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.XSz8H.C0 (nat_lit 2) = true := by quickRfl
theorem cyc1 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.XSz8H.C1 (nat_lit 2) = true := by quickRfl
theorem cyc2 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.XSz8H.C2 (nat_lit 2) = true := by quickRfl
theorem cyc3 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.XSz8H.C3 (nat_lit 2) = true := by quickRfl
theorem cyc4 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.XSz8H.C4 (nat_lit 2) = true := by quickRfl
theorem cyc5 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.XSz8H.C5 (nat_lit 2) = true := by quickRfl

end CFSG.KAct.XSz8H

end
