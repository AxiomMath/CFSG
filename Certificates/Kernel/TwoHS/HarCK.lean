module

public import Certificates.Kernel.TwoHS.HarCD
public import Certificates.Kernel.TwoHS.HYOps
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def cnK (p : Nat) : Bool := canonK 11200 14 (mask 14) (11200 * 14) p

@[expose] noncomputable def pinvY (p : Nat) : Nat := pinvS 11200 14 (mask 14) p

@[expose] noncomputable def invYK (p r : Nat) : Bool :=
  bAnd(cnK p, bAnd(cnK r, invEqK 11200 14 (mask 14) (11200 * 14) p r))

@[expose] noncomputable def G3K : Nat := WK harCW3

@[expose] noncomputable def G5K : Nat := WK harCW5

@[expose] noncomputable def CK : Nat := WK harCWit

@[expose] noncomputable def CKI : Nat := pinvY CK

@[expose] noncomputable def Z1K : Nat := UK [3, 3, 3, 3]

@[expose] noncomputable def C0K : Nat := UK [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]

@[expose] noncomputable def Z2K : Nat := pc C0K Z1K

@[expose] noncomputable def commP (a b : Nat) : Nat := pc (pc a b) (pc (pinvY a) (pinvY b))

@[expose] noncomputable def QK (j : Nat) : Nat :=
  commP (UK (harCQPairs.getD j ([], true)).1) (cond (harCQPairs.getD j ([], true)).2 G3K G5K)

@[expose] noncomputable def CGK (j : Nat) : Nat := [UL 1, UL 2, UL 3, G3K, G5K].getD j 0

theorem harC_base : bAnd(allN 3 (fun j => bAnd(Nat.beq (TE.GI j) (UL (Nat.succ j)),
    bAnd(Nat.beq (TE.G j) idK, invYK (TE.GI j) (TEI j)))),
  bAnd(Nat.beq TE.cnt 1024, bAnd(penumHdK idK TE.cnt 2000 TE.T TE.PL,
  bAnd(allN 6 (fun j => bAnd(Nat.beq (TQ.GI j) (QK j),
    bAnd(Nat.beq (TQ.G j) idK, invYK (TQ.GI j) (TQI j)))),
  bAnd(Nat.beq TQ.cnt 128, bAnd(penumHdK idK TQ.cnt 400 TQ.T TQ.PL,
  bAnd(allN 5 (fun j => bAnd(Nat.beq (TCG j) (CGK j), invYK (TCG j) (TCGI j))),
  bAnd(Nat.blt (r32 TQR 0) TQ.cnt, bAnd(Nat.beq (TQ.T (r32 TQR 0)) (UK harCRoot),
  bAnd(Nat.beq (pc (UK harCRoot) (UK harCRoot)) Z1K,
  bAnd(Nat.beq (pc (pc G3K G3K) G3K) idK, bAnd(bIf(Nat.beq G3K idK, false, true),
  bAnd(Nat.beq (pc (pc (pc (pc G5K G5K) G5K) G5K) G5K) idK, bAnd(bIf(Nat.beq G5K idK, false, true),
  bAnd(Nat.beq (pc G3K Z1K) (pc Z1K G3K), bAnd(Nat.beq (pc G5K Z1K) (pc Z1K G5K),
  bAnd(Nat.beq (pc CK Z1K) (pc Z1K CK), bAnd(invYK CK CKI, bAnd(cnK Z1K, cnK C0K))))))))))))))))))) =
    true := by
  quickRfl

@[expose] noncomputable def peE (k : Nat) : Bool :=
  penumSlK 11200 14 (mask 14) (11200 * 14) true TE.G TE.GI 3 TE.cnt TE.T TE.PL TE.POS TE.SRT TE.SRI
    (Nat.mul 32 k) 32

@[expose] noncomputable def hsE (k : Nat) : Bool :=
  slK TE.cnt (hsortPtK 11200 14 (mask 14) TE.cnt TE.T TE.HS TE.HSI) (Nat.mul 64 k) 64

@[expose] noncomputable def clE (k : Nat) : Bool :=
  slK (Nat.mul TE.cnt 6) (findPtK TE.cnt TE.T (prodQK 11200 14 (mask 14) 6 TE.T (bothK 3 TE.GI TEI))
    TECl) (Nat.mul 128 k) 128

@[expose] noncomputable def peQ (k : Nat) : Bool :=
  penumSlK 11200 14 (mask 14) (11200 * 14) true TQ.G TQ.GI 6 TQ.cnt TQ.T TQ.PL TQ.POS TQ.SRT TQ.SRI
    (Nat.mul 16 k) 16

@[expose] noncomputable def hsQ (k : Nat) : Bool :=
  slK TQ.cnt (hsortPtK 11200 14 (mask 14) TQ.cnt TQ.T TQ.HS TQ.HSI) (Nat.mul 64 k) 64

@[expose] noncomputable def clQ (k : Nat) : Bool :=
  slK (Nat.mul TQ.cnt 12) (findPtK TQ.cnt TQ.T (prodQK 11200 14 (mask 14) 12 TQ.T (bothK 6 TQ.GI TQI))
    TQCl) (Nat.mul 128 k) 128

@[expose] noncomputable def nqQ (k : Nat) : Bool :=
  slK (Nat.mul TQ.cnt 5) (findPtK TQ.cnt TQ.T (conjQK 11200 14 (mask 14) 5 TQ.T TCG TCGI) TQN)
    (Nat.mul 64 k) 64

@[expose] noncomputable def c3At (i : Nat) : Bool :=
  strictB (TE.T i) (fun y => bIf(Nat.beq (pc y y) Z2K,
    strictB (pc (pc CK y) CKI) (fun x => allN TE.cnt (fun q => bIf(Nat.beq (TE.T q) x, false, true))),
    true))

@[expose] noncomputable def c3S (k : Nat) : Bool := slK TE.cnt c3At (Nat.mul 128 k) 128

end CFSG.KD.TwoHS

end
