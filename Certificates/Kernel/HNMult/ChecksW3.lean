module

public import Certificates.Kernel.HNMult.Data
public import Certificates.Data.Kernel.HNMultK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNMult

theorem w74 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 74) (nat_lit 8) = true := by quickRfl

theorem w82 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 82) (nat_lit 2) = true := by quickRfl

theorem w84 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 84) (nat_lit 1) = true := by quickRfl

theorem w85 : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNMult.mul (nat_lit 13) CFSG.KD.FamHNSeed.ONE WD
    (nat_lit 85) (nat_lit 1) = true := by quickRfl

end CFSG.KD.HNMult

end
