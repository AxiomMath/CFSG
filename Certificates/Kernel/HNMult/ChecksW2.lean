module

public import Certificates.Kernel.HNMult.Data
public import Certificates.Data.Kernel.HNMultK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNMult

theorem w57 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 57) (nat_lit 3) = true := by quickRfl

theorem w60 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 60) (nat_lit 2) = true := by quickRfl

theorem w62 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 62) (nat_lit 2) = true := by quickRfl

theorem w64 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 64) (nat_lit 1) = true := by quickRfl

theorem w65 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 65) (nat_lit 9) = true := by quickRfl

end CFSG.KD.HNMult

end
