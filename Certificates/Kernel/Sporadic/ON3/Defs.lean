
module

public import Certificates.Kernel.Sporadic.ON3.Data
public import Certificates.Kernel.Sporadic.ON.LvData
public import Certificates.Data.Kernel.Spor.ChainK
public import CFSG.Certificates.Kernel.Spor.CBComm

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.CB CFSG.KS.CH
open CertificateChecks.KernelSpor.ON (TT UU stepF invF PARf LABf)

@[expose] noncomputable def ZT (x : Nat) : Nat := tab ON3T.Z x
@[expose] noncomputable def QT (x : Nat) : Nat := tab ON3T.Q x
@[expose] noncomputable def CT (x : Nat) : Nat := tab ON3T.C x
@[expose] noncomputable def CIT (x : Nat) : Nat := tab ON3T.CI x
@[expose] noncomputable def D1T (x : Nat) : Nat := tab ON3T.D1 x
@[expose] noncomputable def D2T (x : Nat) : Nat := tab ON3T.D2 x
@[expose] noncomputable def D3T (x : Nat) : Nat := tab ON3T.D3 x
@[expose] noncomputable def D4T (x : Nat) : Nat := tab ON3T.D4 x
@[expose] noncomputable def M2T (x : Nat) : Nat := tab ON3T.M2 x
@[expose] noncomputable def M3T (x : Nat) : Nat := tab ON3T.M3 x
@[expose] noncomputable def L1T (x : Nat) : Nat := tab ON3T.L1 x
@[expose] noncomputable def L2T (x : Nat) : Nat := tab ON3T.L2 x
@[expose] noncomputable def WT (x : Nat) : Nat := tab ON3T.W x

@[expose] noncomputable def DT (j x : Nat) : Nat :=
  nIf(Nat.beq j 0, D1T x, nIf(Nat.beq j 1, D2T x, nIf(Nat.beq j 2, D3T x, D4T x)))

@[expose] noncomputable def trW (k x : Nat) : Nat := trace TT UU (ON3W.WC k) (ON3W.WL k) x

@[expose] noncomputable def tG (h x : Nat) : Nat := trW (Nat.add (nat_lit 11) h) x
@[expose] noncomputable def tGI (h x : Nat) : Nat := trW (Nat.add (nat_lit 34) h) x
@[expose] noncomputable def tS6 (x : Nat) : Nat := trace tG tGI (ON3W.WC 17) (ON3W.WL 17) x
@[expose] noncomputable def tS6I (x : Nat) : Nat := trace tG tGI (ON3W.WC 40) (ON3W.WL 40) x
@[expose] noncomputable def tG7 (h x : Nat) : Nat := nIf(Nat.blt h 6, tG h x, tS6 x)
@[expose] noncomputable def tGI7 (h x : Nat) : Nat := nIf(Nat.blt h 6, tGI h x, tS6I x)
@[expose] noncomputable def tS7 (x : Nat) : Nat := trace tG7 tGI7 (ON3W.WC 18) (ON3W.WL 18) x
@[expose] noncomputable def tS7I (x : Nat) : Nat := trace tG7 tGI7 (ON3W.WC 41) (ON3W.WL 41) x
@[expose] noncomputable def tF (j x : Nat) : Nat := nIf(Nat.blt j 7, tG7 j x, tS7 x)
@[expose] noncomputable def tFI (j x : Nat) : Nat := nIf(Nat.blt j 7, tGI7 j x, tS7I x)

@[expose] noncomputable def mG (h x : Nat) : Nat :=
  nIf(Nat.beq h 0, ZT x, nIf(Nat.beq h 1, M2T x, M3T x))
@[expose] noncomputable def mGI (h x : Nat) : Nat :=
  nIf(Nat.beq h 0, ZT x, nIf(Nat.beq h 1, trW 30 x, trW 31 x))
@[expose] noncomputable def mS3 (x : Nat) : Nat := trace mG mGI (ON3W.WC 19) (ON3W.WL 19) x
@[expose] noncomputable def mS3I (x : Nat) : Nat := trace mG mGI (ON3W.WC 42) (ON3W.WL 42) x
@[expose] noncomputable def mG4 (h x : Nat) : Nat := nIf(Nat.blt h 3, mG h x, mS3 x)
@[expose] noncomputable def mGI4 (h x : Nat) : Nat := nIf(Nat.blt h 3, mGI h x, mS3I x)
@[expose] noncomputable def mS4 (x : Nat) : Nat := trace mG4 mGI4 (ON3W.WC 20) (ON3W.WL 20) x
@[expose] noncomputable def mS4I (x : Nat) : Nat := trace mG4 mGI4 (ON3W.WC 43) (ON3W.WL 43) x
@[expose] noncomputable def mF (j x : Nat) : Nat := nIf(Nat.blt j 4, mG4 j x, mS4 x)
@[expose] noncomputable def mFI (j x : Nat) : Nat := nIf(Nat.blt j 4, mGI4 j x, mS4I x)

@[expose] noncomputable def lG (h x : Nat) : Nat := nIf(Nat.beq h 0, L1T x, L2T x)
@[expose] noncomputable def lGI (h x : Nat) : Nat := nIf(Nat.beq h 0, trW 32 x, trW 33 x)
@[expose] noncomputable def lS2 (x : Nat) : Nat := trace lG lGI (ON3W.WC 21) (ON3W.WL 21) x
@[expose] noncomputable def lS2I (x : Nat) : Nat := trace lG lGI (ON3W.WC 44) (ON3W.WL 44) x
@[expose] noncomputable def lG3 (h x : Nat) : Nat := nIf(Nat.blt h 2, lG h x, lS2 x)
@[expose] noncomputable def lGI3 (h x : Nat) : Nat := nIf(Nat.blt h 2, lGI h x, lS2I x)
@[expose] noncomputable def lS3 (x : Nat) : Nat := trace lG3 lGI3 (ON3W.WC 22) (ON3W.WL 22) x
@[expose] noncomputable def lS3I (x : Nat) : Nat := trace lG3 lGI3 (ON3W.WC 45) (ON3W.WL 45) x
@[expose] noncomputable def lF (j x : Nat) : Nat := nIf(Nat.blt j 3, lG3 j x, lS3 x)
@[expose] noncomputable def lFI (j x : Nat) : Nat := nIf(Nat.blt j 3, lGI3 j x, lS3I x)

@[expose] noncomputable def tabAt (x : Nat) : Bool :=
  strictB (ZT x) fun z => strictB (QT x) fun q => strictB (CT x) fun c => strictB (CIT x) fun ci =>
  strictB (WT x) fun w =>
  bAnd(Nat.beq z (trW 0 x), bAnd(Nat.beq q (trW 1 x), bAnd(Nat.beq c (trW 2 x),
  bAnd(Nat.beq (CIT c) x,
  bAnd(Nat.beq (D1T x) (trW 3 x), bAnd(Nat.beq (D2T x) (trW 4 x), bAnd(Nat.beq (D3T x) (trW 5 x),
  bAnd(Nat.beq (D4T x) (trW 6 x), bAnd(Nat.beq (M2T x) (trW 7 x), bAnd(Nat.beq (M3T x) (trW 8 x),
  bAnd(Nat.beq (L1T x) (trW 9 x), bAnd(Nat.beq (L2T x) (trW 10 x),
  bAnd(Nat.beq w (CT (QT (QT ci))),
  bAnd(Nat.beq (ZT z) x, bAnd(Nat.beq (M2T z) (ZT (M2T x)), bAnd(Nat.beq (M3T z) (ZT (M3T x)),
  bAnd(Nat.beq (QT (QT (QT q))) x, bAnd(Nat.beq (L1T q) (QT (L1T x)),
  bAnd(Nat.beq (L2T q) (QT (L2T x)), bAnd(Nat.beq (D1T x) (CT (ZT ci)),
  allN 4 fun j => Nat.beq (WT (DT j x)) (DT j w)))))))))))))))))))))

@[expose] noncomputable def tabS (s : Nat) : Bool :=
  allN (nat_lit 2046) fun d => tabAt (Nat.add (Nat.mul s (nat_lit 2046)) d)

@[expose] noncomputable def fxF (q : Nat) : Nat :=
  nIf(Nat.blt q 245520, nIf(Nat.beq (ZT q) q, 1, 0), 0)

@[expose] noncomputable def fxV (s : Nat) : Nat := List.getD [28, 35, 35, 37, 33, 26, 21, 25] s 0

@[expose] noncomputable def fxOK (s : Nat) : Bool :=
  Nat.beq (sumR2 fxF (Nat.mul 30720 s) 480) (fxV s)

@[expose] noncomputable def ccA (k : Nat) : Nat := trK (stepF 2) (PARf 2) (LABf 2) 36 k (ZT 227759)

@[expose] noncomputable def ccX (k : Nat) : Nat :=
  ccF ZT ccA (stepF 1) (invF 1) (PARf 1) (LABf 1) 52136 (stepF 2) (PARf 2) (LABf 2) 36 227759
    100817 k

@[expose] noncomputable def ccV (s : Nat) : Nat :=
  List.getD [23, 25, 28, 30, 33, 28, 20, 34, 32, 22, 22, 32, 25, 26, 22, 26, 30, 26, 20, 25, 22, 23, 29,
    31, 28, 10] s 0

@[expose] noncomputable def ccOK (s : Nat) : Bool :=
  Nat.beq (sumR2 ccX (Nat.mul 2048 s) 32) (ccV s)

@[expose] noncomputable def bB (k : Nat) : Nat :=
  nIf(Nat.beq k 0, nat_lit 0, nIf(Nat.beq k 1, nat_lit 227759, nat_lit 100817))

@[expose] noncomputable def lv3 (T0 T1 T2 : Nat → Nat) (i k : Nat) : Nat :=
  nIf(Nat.beq i 0, tab T0 k, nIf(Nat.beq i 1, tab T1 k, tab T2 k))

@[expose] noncomputable def nat3 (a b c i : Nat) : Nat :=
  nIf(Nat.beq i 0, a, nIf(Nat.beq i 1, b, c))

@[expose] noncomputable def tPTS : Nat → Nat → Nat := lv3 ON3LT.PTS0 ON3LT.PTS1 ON3LT.PTS2
@[expose] noncomputable def tPOS : Nat → Nat → Nat := lv3 ON3LT.POS0 ON3LT.POS1 ON3LT.POS2
@[expose] noncomputable def tPAR : Nat → Nat → Nat := lv3 ON3LT.PAR0 ON3LT.PAR1 ON3LT.PAR2
@[expose] noncomputable def tLAB : Nat → Nat → Nat := lv3 ON3LT.LAB0 ON3LT.LAB1 ON3LT.LAB2
@[expose] noncomputable def tMr : Nat → Nat := nat3 ON3LT.M0 ON3LT.M1 ON3LT.M2
@[expose] noncomputable def tIDX (i t : Nat) : Nat := nIf(Nat.beq i 0, t, Nat.add 6 t)
@[expose] noncomputable def tLEN : Nat → Nat := nat3 8 2 0

@[expose] noncomputable def mPTS : Nat → Nat → Nat := lv3 ON3LM.PTS0 ON3LM.PTS1 ON3LM.PTS2
@[expose] noncomputable def mPOS : Nat → Nat → Nat := lv3 ON3LM.POS0 ON3LM.POS1 ON3LM.POS2
@[expose] noncomputable def mPAR : Nat → Nat → Nat := lv3 ON3LM.PAR0 ON3LM.PAR1 ON3LM.PAR2
@[expose] noncomputable def mLAB : Nat → Nat → Nat := lv3 ON3LM.LAB0 ON3LM.LAB1 ON3LM.LAB2
@[expose] noncomputable def mMr : Nat → Nat := nat3 ON3LM.M0 ON3LM.M1 ON3LM.M2
@[expose] noncomputable def mIDX (i t : Nat) : Nat :=
  nIf(Nat.beq i 0, t, nIf(Nat.blt t 2, t, Nat.succ t))
@[expose] noncomputable def mLEN : Nat → Nat := nat3 5 4 0

@[expose] noncomputable def lPTS : Nat → Nat → Nat := lv3 ON3LL.PTS0 ON3LL.PTS1 ON3LL.PTS2
@[expose] noncomputable def lPOS : Nat → Nat → Nat := lv3 ON3LL.POS0 ON3LL.POS1 ON3LL.POS2
@[expose] noncomputable def lPAR : Nat → Nat → Nat := lv3 ON3LL.PAR0 ON3LL.PAR1 ON3LL.PAR2
@[expose] noncomputable def lLAB : Nat → Nat → Nat := lv3 ON3LL.LAB0 ON3LL.LAB1 ON3LL.LAB2
@[expose] noncomputable def lMr : Nat → Nat := nat3 ON3LL.M0 ON3LL.M1 ON3LL.M2
@[expose] noncomputable def lIDX (i t : Nat) : Nat := nIf(Nat.beq i 0, t, Nat.add 2 t)
@[expose] noncomputable def lLEN : Nat → Nat := nat3 4 2 0

@[expose] noncomputable def ptT (i s : Nat) : Bool :=
  cbPtRange 245520 (tMr i) (Nat.mul 2 (tLEN i)) (stepX tF tFI (tIDX i) (tLEN i)) (tPTS i) (tPOS i)
    (tPAR i) (tLAB i) (Nat.mul s 16) 16

@[expose] noncomputable def ptM (i s : Nat) : Bool :=
  cbPtRange 245520 (mMr i) (Nat.mul 2 (mLEN i)) (stepX mF mFI (mIDX i) (mLEN i)) (mPTS i) (mPOS i)
    (mPAR i) (mLAB i) (Nat.mul s 16) 16

@[expose] noncomputable def ptL (i s : Nat) : Bool :=
  cbPtRange 245520 (lMr i) (Nat.mul 2 (lLEN i)) (stepX lF lFI (lIDX i) (lLEN i)) (lPTS i) (lPOS i)
    (lPAR i) (lLAB i) (Nat.mul s 16) 16

@[expose] noncomputable def ptT0 (s : Nat) : Bool := ptT 0 s
@[expose] noncomputable def ptT1 (s : Nat) : Bool := ptT 1 s
@[expose] noncomputable def ptT2 (s : Nat) : Bool := ptT 2 s
@[expose] noncomputable def ptM0 (s : Nat) : Bool := ptM 0 s
@[expose] noncomputable def ptM1 (s : Nat) : Bool := ptM 1 s
@[expose] noncomputable def ptM2 (s : Nat) : Bool := ptM 2 s
@[expose] noncomputable def ptL0 (s : Nat) : Bool := ptL 0 s
@[expose] noncomputable def ptL1 (s : Nat) : Bool := ptL 1 s
@[expose] noncomputable def ptL2 (s : Nat) : Bool := ptL 2 s

@[expose] noncomputable def posC (m : Nat) (PTS POS : Nat → Nat) (s : Nat) : Bool :=
  allN (nat_lit 30690) fun d => cbPos (nat_lit 245520) m PTS POS (Nat.add (Nat.mul s (nat_lit 30690)) d)

@[expose] noncomputable def posS (u : Nat) : Bool :=
  strictB (Nat.mod u 8) fun s => strictB (Nat.div u 8) fun v => strictB (Nat.mod v 3) fun i =>
  strictB (Nat.div v 3) fun c =>
  bIf(Nat.beq c 0, posC (tMr i) (tPTS i) (tPOS i) s,
    bIf(Nat.beq c 1, posC (mMr i) (mPTS i) (mPOS i) s, posC (lMr i) (lPTS i) (lPOS i) s))

@[expose] noncomputable def siftT (g : Nat → Nat) : Bool :=
  sift3 tPOS tPAR tLAB tMr (fun i => invX tF tFI (tIDX i) (tLEN i)) (g (bB 0)) (g (bB 1)) (g (bB 2))

@[expose] noncomputable def siftM (g : Nat → Nat) : Bool :=
  sift3 mPOS mPAR mLAB mMr (fun i => invX mF mFI (mIDX i) (mLEN i)) (g (bB 0)) (g (bB 1)) (g (bB 2))

@[expose] noncomputable def siftL (g : Nat → Nat) : Bool :=
  sift3 lPOS lPAR lLAB lMr (fun i => invX lF lFI (lIDX i) (lLEN i)) (g (bB 0)) (g (bB 1)) (g (bB 2))

@[expose] noncomputable def headsOK : Bool :=
  allN 3 fun i => bAnd(idxOK tF 8 bB i (tIDX i) (tLEN i), bAnd(idxOK mF 5 bB i (mIDX i) (mLEN i),
    bAnd(idxOK lF 4 bB i (lIDX i) (lLEN i),
    bAnd(cbHead 245520 (tMr i) (bB i) (tPTS i) (tPAR i) (tLAB i),
    bAnd(cbHead 245520 (mMr i) (bB i) (mPTS i) (mPAR i) (mLAB i),
      cbHead 245520 (lMr i) (bB i) (lPTS i) (lPAR i) (lLAB i))))))

@[expose] noncomputable def siftsOK : Bool :=
  bAnd(siftT ZT, bAnd(siftL QT, bAnd(siftM L1T, bAnd(siftM L2T,
    allN 4 fun j => bAnd(siftM (DT j), siftM fun x => CIT (DT j (CT x)))))))

end CertificateChecks.KernelSpor.ON3

end
