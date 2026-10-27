module

public import Certificates.Kernel.M24Three.Recs
public import Certificates.Data.Kernel.Spor.MulHQ
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option maxRecDepth 400000

public section

namespace CFSG.KD.M24Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 24 5 (mask 5) (24 * 5) p

@[expose] noncomputable def invK (p q : Nat) : Bool :=
  bAnd(cK p, bAnd(cK q, invEqK 24 5 (mask 5) (24 * 5) p q))

@[expose] noncomputable def elK (j : Nat) : Bool :=
  bAnd(invK (EL j) (EI j),
    Nat.beq (EL j) (wperm 24 5 (mask 5) (GN 0) (GN 1) (GN 2) (GN 3) (WL j) (LN j)))

@[expose] noncomputable def cmK (p q : Nat) : Bool := eq22 24 5 (mask 5) p q q p

@[expose] noncomputable def fix3K (p i j k : Nat) : Bool :=
  bAnd(Nat.beq (pg 5 (mask 5) p i) i, bAnd(Nat.beq (pg 5 (mask 5) p j) j,
    Nat.beq (pg 5 (mask 5) p k) k))

theorem ch12613_el : bAnd(invK (GN 0) (GN 2), bAnd(invK (GN 1) (GN 3), allN 24 elK)) = true := by
  quickRfl

theorem ch12613_bind :
    bAnd(Nat.beq OA.k 2, bAnd(Nat.beq (OA.G 0) (EL 8), bAnd(Nat.beq (OA.G 1) (EL 9),
    bAnd(Nat.beq (OA.GI 0) (EI 8), bAnd(Nat.beq (OA.GI 1) (EI 9), bAnd(Nat.beq OA.R (EL 0),
    bAnd(Nat.beq OA.cnt 336, bAnd(penumHdK OA.R OA.cnt 2000 OA.T OA.PL,
    bAnd(Nat.beq OB.k 2, bAnd(Nat.beq (OB.G 0) (EL 10), bAnd(Nat.beq (OB.G 1) (EL 11),
    bAnd(Nat.beq (OB.GI 0) (EI 10), bAnd(Nat.beq (OB.GI 1) (EI 11), bAnd(Nat.beq OB.R (EL 1),
    bAnd(Nat.beq OB.cnt 960, bAnd(penumHdK OB.R OB.cnt 2000 OB.T OB.PL,
    bAnd(Nat.beq CA.k 2, bAnd(Nat.beq (CA.G 0) (pidn 24 5), bAnd(Nat.beq (CA.G 1) (pidn 24 5),
    bAnd(Nat.beq (CA.GI 0) (EL 4), bAnd(Nat.beq (CA.GI 1) (EL 5), bAnd(Nat.beq CA.R (pidn 24 5),
    bAnd(Nat.beq CA.cnt 1080, bAnd(penumHdK CA.R CA.cnt 2000 CA.T CA.PL,
    bAnd(Nat.beq CB.k 2, bAnd(Nat.beq (CB.G 0) (pidn 24 5), bAnd(Nat.beq (CB.G 1) (pidn 24 5),
    bAnd(Nat.beq (CB.GI 0) (EL 6), bAnd(Nat.beq (CB.GI 1) (EL 7), bAnd(Nat.beq CB.R (pidn 24 5),
    bAnd(Nat.beq CB.cnt 504, bAnd(penumHdK CB.R CB.cnt 2000 CB.T CB.PL,
    bAnd(Nat.beq S.k 2, bAnd(Nat.beq (S.G 0) (pidn 24 5), bAnd(Nat.beq (S.G 1) (pidn 24 5),
    bAnd(Nat.beq (S.GI 0) (EL 2), bAnd(Nat.beq (S.GI 1) (EL 3), bAnd(Nat.beq S.R (pidn 24 5),
    bAnd(Nat.beq S.cnt 27, bAnd(penumHdK S.R S.cnt 100 S.T S.PL,
    bAnd(Nat.beq (SI 0) (EI 2), Nat.beq (SI 1) (EI 3)))))))))))))))))))))))))))))))))))))))))) =
      true := by
  quickRfl

theorem ch12613_fix :
    bAnd(fix3K (EL 8) 0 3 5, bAnd(fix3K (EL 9) 0 3 5, bAnd(fix3K (EL 10) 0 17 13,
    bAnd(fix3K (EL 11) 0 17 13, bAnd(Nat.beq (pg 5 (mask 5) (EL 0) 0) 3,
    bAnd(Nat.beq (pg 5 (mask 5) (EL 0) 3) 5, bAnd(Nat.beq (pg 5 (mask 5) (EL 1) 0) 17,
    Nat.beq (pg 5 (mask 5) (EL 1) 17) 13))))))) = true := by
  quickRfl

theorem ch12613_comm :
    bAnd(cmK (EL 4) (EL 0), bAnd(cmK (EL 5) (EL 0), bAnd(cmK (EL 15) (EL 0),
    bAnd(cmK (EL 16) (EL 0), bAnd(cmK (EL 17) (EL 0), bAnd(cmK (EL 6) (EL 1),
    bAnd(cmK (EL 7) (EL 1), bAnd(cmK (EL 21) (EL 1), bAnd(cmK (EL 22) (EL 1),
    cmK (EL 23) (EL 1)))))))))) = true := by
  quickRfl

@[expose] noncomputable def oaE (i : Nat) : Bool := penumSlK 24 5 (mask 5) (24 * 5) true OA.G OA.GI
  2 OA.cnt OA.T OA.PL OA.POS OA.SRT OA.SRI (Nat.mul i 56) 56
@[expose] noncomputable def oaH (i : Nat) : Bool :=
  slK OA.cnt (hsortPtK 24 5 (mask 5) OA.cnt OA.T OA.HS OA.HSI) (Nat.mul i 56) 56
@[expose] noncomputable def obE (i : Nat) : Bool := penumSlK 24 5 (mask 5) (24 * 5) true OB.G OB.GI
  2 OB.cnt OB.T OB.PL OB.POS OB.SRT OB.SRI (Nat.mul i 64) 64
@[expose] noncomputable def obH (i : Nat) : Bool :=
  slK OB.cnt (hsortPtK 24 5 (mask 5) OB.cnt OB.T OB.HS OB.HSI) (Nat.mul i 64) 64
@[expose] noncomputable def caE (i : Nat) : Bool := penumSlK 24 5 (mask 5) (24 * 5) true CA.G CA.GI
  2 CA.cnt CA.T CA.PL CA.POS CA.SRT CA.SRI (Nat.mul i 60) 60
@[expose] noncomputable def caH (i : Nat) : Bool :=
  slK CA.cnt (hsortPtK 24 5 (mask 5) CA.cnt CA.T CA.HS CA.HSI) (Nat.mul i 60) 60
@[expose] noncomputable def cbE (i : Nat) : Bool := penumSlK 24 5 (mask 5) (24 * 5) true CB.G CB.GI
  2 CB.cnt CB.T CB.PL CB.POS CB.SRT CB.SRI (Nat.mul i 56) 56
@[expose] noncomputable def cbH (i : Nat) : Bool :=
  slK CB.cnt (hsortPtK 24 5 (mask 5) CB.cnt CB.T CB.HS CB.HSI) (Nat.mul i 56) 56

#kc_slice_range oaE ch12613oaE_ 0 6
#kc_slice_range oaH ch12613oaH_ 0 6
#kc_slice_range obE ch12613obE_ 0 15
#kc_slice_range obH ch12613obH_ 0 15
#kc_slice_range caE ch12613caE_ 0 18
#kc_slice_range caH ch12613caH_ 0 18
#kc_slice_range cbE ch12613cbE_ 0 9
#kc_slice_range cbH ch12613cbH_ 0 9

theorem ch12613sE : penumSlK 24 5 (mask 5) (24 * 5) true S.G S.GI 2 S.cnt S.T S.PL S.POS S.SRT
    S.SRI 0 S.cnt = true := by quickRfl
theorem ch12613sH : slK S.cnt (hsortPtK 24 5 (mask 5) S.cnt S.T S.HS S.HSI) 0 S.cnt = true := by
  quickRfl
theorem ch12613sCl : slK (Nat.mul S.cnt 4)
    (findPtK S.cnt S.T (prodQK 24 5 (mask 5) 4 S.T (bothK 2 S.GI SI)) SCl) 0
      (Nat.mul S.cnt 4) = true := by quickRfl

end CFSG.KD.M24Three

end
