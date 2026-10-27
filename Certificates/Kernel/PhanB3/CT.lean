module

public import Certificates.Kernel.PhanB3.CTData
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.PhanB3CT

open CFSG.KC.MiscCoset.Act

theorem all : allR (nat_lit 0) (nat_lit 1120)
    (pointOK CFSG.KAct.PhanB3CT.A (nat_lit 14) (nat_lit 1120)
      (CFSG.KAct.PhanB3CT.R ++ CFSG.KAct.PhanB3CT.RD ++ CFSG.KAct.PhanB3CT.RC)) = true := by
  allR_blocks 32

theorem ch270007_point_x0 : notB (pointOK CFSG.KAct.PhanB3CT.A (nat_lit 14) (nat_lit 1120)
    [[0]] (nat_lit 0)) = true := by quickRfl

theorem ch270007_point_short : notB (pointOK CFSG.KAct.PhanB3CT.A (nat_lit 14) (nat_lit 1119)
    [] (nat_lit 1118)) = true := by quickRfl

theorem ch270007_ct_def_short : notB (pointOK CFSG.KAct.PhanB3CT.A (nat_lit 14) (nat_lit 1120)
    [CFSG.KAct.PhanB3CT.RD.head!.dropLast] (nat_lit 0)) = true := by quickRfl

theorem ch270007_ct_t2 : notB (pointOK CFSG.KAct.PhanB3CT.A (nat_lit 14) (nat_lit 1120)
    [[26]] (nat_lit 0)) = true := by quickRfl

end CFSG.KAct.PhanB3CT

end
