module

public import Certificates.Kernel.HNF26729.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFWords

open CFSG.EvenSporadicStandard.Solomon78 CFSG.KD.HNF26729 CFSG.KC.HNF26720

#kc_natval G1 := wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
  CFSG.KD.FamHNSeed.ONE hnfW1
#kc_natval G1i := wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
  CFSG.KD.FamHNSeed.ONE (invW hnfW1)
#kc_natval G2 := wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
  CFSG.KD.FamHNSeed.ONE hnfW2
#kc_natval G2i := wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
  CFSG.KD.FamHNSeed.ONE (invW hnfW2)

theorem G1_eq : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE hnfW1 = G1 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem G1i_eq : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE (invW hnfW1) = G1i := Nat.eq_of_beq_eq_true (by quickRfl)

theorem G2_eq : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE hnfW2 = G2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem G2i_eq : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE (invW hnfW2) = G2i := Nat.eq_of_beq_eq_true (by quickRfl)

end CFSG.KD.HNFWords

end
