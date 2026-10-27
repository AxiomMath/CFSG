module

public import Certificates.Kernel.HNMult.Data
public import Certificates.Data.Kernel.HNMultK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNMult

theorem w8 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 8) (nat_lit 2) = true := by quickRfl

theorem w10 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 10) (nat_lit 14) = true := by quickRfl

theorem w24 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 24) (nat_lit 23) = true := by quickRfl

theorem w47 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 47) (nat_lit 6) = true := by quickRfl

theorem w53 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 53) (nat_lit 4) = true := by quickRfl

end CFSG.KD.HNMult

end
