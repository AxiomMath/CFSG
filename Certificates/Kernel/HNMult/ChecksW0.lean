module

public import Certificates.Kernel.HNMult.Data
public import Certificates.Data.Kernel.HNMultK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNMult

theorem w0 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 0) (nat_lit 2) = true := by quickRfl

theorem w2 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 2) (nat_lit 2) = true := by quickRfl

theorem w4 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 4) (nat_lit 1) = true := by quickRfl

theorem w5 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 5) (nat_lit 1) = true := by quickRfl

theorem w6 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 6) (nat_lit 1) = true := by quickRfl

theorem w7 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 7) (nat_lit 1) = true := by quickRfl

end CFSG.KD.HNMult

end
