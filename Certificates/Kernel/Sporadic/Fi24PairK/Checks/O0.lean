module

public import Certificates.Kernel.Sporadic.Fi24PairK.Data
import CFSG.Certificates.Kernel.Common.SliceRange

public section

#kc_slice_range CFSG.KD.Fi24PairK.och CFSG.KD.Fi24PairK.Ck.o 0 2
#kc_slice_range CFSG.KD.Fi24PairK.och CFSG.KD.Fi24PairK.Ck.o 3 12
#kc_slice_range CFSG.KD.Fi24PairK.fch CFSG.KD.Fi24PairK.Ck.f 0 12

namespace CFSG.KD.Fi24PairK

open CFSG.KC CFSG.KC.Fi24PairK

theorem Ck.o2d : (lvW (chOf (nat_lit 2)) (lvOf (nat_lit 2))).all (dirOK net) = true := by quickRfl

theorem Ck.o2a : Nat.beq (schWP NV (lvW (chOf (nat_lit 2)) (lvOf (nat_lit 2)))
    (nthLP schLA (nat_lit 2)) (Nat.shiftLeft (nat_lit 1) (chOf (nat_lit 2)).base[lvOf (nat_lit 2)]!))
    (nthN midL (nat_lit 2)) = true := by quickRfl

theorem Ck.o2b : Nat.beq (popcount (schWP NV (lvW (chOf (nat_lit 2)) (lvOf (nat_lit 2)))
    (nthLP schLP (nat_lit 2)) (nthN midL (nat_lit 2))) (nat_lit 524288))
    ((chOf (nat_lit 2)).sizes.getD (lvOf (nat_lit 2)) 0) = true := by quickRfl

theorem Ck.o2 : och (nat_lit 2) = true := och_of_mp Ck.o2d Ck.o2a Ck.o2b

end CFSG.KD.Fi24PairK

end
