module

public import Certificates.Kernel.HNMult.Data
public import Certificates.Data.Kernel.HNMultK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNMult

theorem hroots : CFSG.KC.Ord.rootsOK RB CFSG.KD.HNMult.vld (nat_lit 1) (nat_lit 14) = true := by
  quickRfl

theorem hinv : CFSG.KC.Ord.invsOK RB CFSG.KD.HNMult.mul CFSG.KD.HNMult.vld (nat_lit 13)
    CFSG.KD.FamHNSeed.ONE = true := by
  quickRfl

theorem hA : Nat.beq (RB (nat_lit 1)) (CFSG.KD.FamHNSeed.RW (nat_lit 1)) = true := by quickRfl

theorem hB : Nat.beq (RB (nat_lit 2)) (CFSG.KD.FamHNSeed.RW (nat_lit 2)) = true := by quickRfl

end CFSG.KD.HNMult

end
