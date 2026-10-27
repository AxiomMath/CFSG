
module

public import Certificates.Kernel.Sporadic.ON4.Data
public import Certificates.Kernel.Sporadic.ON4.WordsData
public import Certificates.Kernel.Sporadic.ON3.Defs
public import Certificates.Data.Kernel.Spor.ChainSK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.CB CFSG.KS.CH
open CertificateChecks.KernelSpor.ON3 (ZT CT CIT M2T M3T L1T L2T trW tG tGI tF tFI mG mGI mF mFI
  lG lGI lF lFI lv3 nat3 bB tPTS tPOS tPAR tLAB tMr tIDX tLEN mPTS mPOS mPAR mLAB mMr mIDX mLEN
  lPTS lPOS lPAR lLAB lMr lIDX lLEN)

@[expose] noncomputable def mcX (y : Nat) : Nat := M3T (M2T (mGI 2 (mGI 1 y)))
@[expose] noncomputable def mcXI (y : Nat) : Nat := M2T (M3T (mGI 1 (mGI 2 y)))
@[expose] noncomputable def mcO (j y : Nat) : Nat :=
  nIf(Nat.beq j 0, mcX y, nIf(Nat.beq j 1, M2T (mcX (mGI 1 y)), M3T (mcX (mGI 2 y))))
@[expose] noncomputable def mcOI (j y : Nat) : Nat :=
  nIf(Nat.beq j 0, mcXI y, nIf(Nat.beq j 1, M2T (mcXI (mGI 1 y)), M3T (mcXI (mGI 2 y))))
@[expose] noncomputable def mc3 (x : Nat) : Nat := trace mcO mcOI (ON4W.WC 0) (ON4W.WL 0) x
@[expose] noncomputable def mc3I (x : Nat) : Nat := trace mcO mcOI (ON4W.WC 8) (ON4W.WL 8) x
@[expose] noncomputable def mcO4 (j x : Nat) : Nat := nIf(Nat.blt j 3, mcO j x, mc3 x)
@[expose] noncomputable def mcOI4 (j x : Nat) : Nat := nIf(Nat.blt j 3, mcOI j x, mc3I x)
@[expose] noncomputable def mc4 (x : Nat) : Nat := trace mcO4 mcOI4 (ON4W.WC 1) (ON4W.WL 1) x
@[expose] noncomputable def mc4I (x : Nat) : Nat := trace mcO4 mcOI4 (ON4W.WC 9) (ON4W.WL 9) x
@[expose] noncomputable def mcF (j x : Nat) : Nat := nIf(Nat.blt j 4, mcO4 j x, mc4 x)
@[expose] noncomputable def mcFI (j x : Nat) : Nat := nIf(Nat.blt j 4, mcOI4 j x, mc4I x)

@[expose] noncomputable def lcX (y : Nat) : Nat := L2T (L1T (lGI 1 (lGI 0 y)))
@[expose] noncomputable def lcXI (y : Nat) : Nat := L1T (L2T (lGI 0 (lGI 1 y)))
@[expose] noncomputable def lcO (j y : Nat) : Nat :=
  nIf(Nat.beq j 0, lcX y, nIf(Nat.beq j 1, L1T (lcX (lGI 0 y)), L2T (lcX (lGI 1 y))))
@[expose] noncomputable def lcOI (j y : Nat) : Nat :=
  nIf(Nat.beq j 0, lcXI y, nIf(Nat.beq j 1, L1T (lcXI (lGI 0 y)), L2T (lcXI (lGI 1 y))))
@[expose] noncomputable def lc3 (x : Nat) : Nat := trace lcO lcOI (ON4W.WC 2) (ON4W.WL 2) x
@[expose] noncomputable def lc3I (x : Nat) : Nat := trace lcO lcOI (ON4W.WC 10) (ON4W.WL 10) x
@[expose] noncomputable def lcO4 (j x : Nat) : Nat := nIf(Nat.blt j 3, lcO j x, lc3 x)
@[expose] noncomputable def lcOI4 (j x : Nat) : Nat := nIf(Nat.blt j 3, lcOI j x, lc3I x)
@[expose] noncomputable def lc4 (x : Nat) : Nat := trace lcO4 lcOI4 (ON4W.WC 3) (ON4W.WL 3) x
@[expose] noncomputable def lc4I (x : Nat) : Nat := trace lcO4 lcOI4 (ON4W.WC 11) (ON4W.WL 11) x
@[expose] noncomputable def lcO5 (j x : Nat) : Nat := nIf(Nat.blt j 4, lcO4 j x, lc4 x)
@[expose] noncomputable def lcOI5 (j x : Nat) : Nat := nIf(Nat.blt j 4, lcOI4 j x, lc4I x)
@[expose] noncomputable def lc5 (x : Nat) : Nat := trace lcO5 lcOI5 (ON4W.WC 4) (ON4W.WL 4) x
@[expose] noncomputable def lc5I (x : Nat) : Nat := trace lcO5 lcOI5 (ON4W.WC 12) (ON4W.WL 12) x
@[expose] noncomputable def lcF (j x : Nat) : Nat := nIf(Nat.blt j 5, lcO5 j x, lc5 x)
@[expose] noncomputable def lcFI (j x : Nat) : Nat := nIf(Nat.blt j 5, lcOI5 j x, lc5I x)

@[expose] noncomputable def jO (j y : Nat) : Nat :=
  nIf(Nat.blt j 3, mG j y, CT (mG (Nat.sub j 3) (CIT y)))
@[expose] noncomputable def jOI (j y : Nat) : Nat :=
  nIf(Nat.blt j 3, mGI j y, CT (mGI (Nat.sub j 3) (CIT y)))
@[expose] noncomputable def j6 (x : Nat) : Nat := trace jO jOI (ON4W.WC 5) (ON4W.WL 5) x
@[expose] noncomputable def j6I (x : Nat) : Nat := trace jO jOI (ON4W.WC 13) (ON4W.WL 13) x
@[expose] noncomputable def jO7 (j x : Nat) : Nat := nIf(Nat.blt j 6, jO j x, j6 x)
@[expose] noncomputable def jOI7 (j x : Nat) : Nat := nIf(Nat.blt j 6, jOI j x, j6I x)
@[expose] noncomputable def j7 (x : Nat) : Nat := trace jO7 jOI7 (ON4W.WC 6) (ON4W.WL 6) x
@[expose] noncomputable def j7I (x : Nat) : Nat := trace jO7 jOI7 (ON4W.WC 14) (ON4W.WL 14) x
@[expose] noncomputable def jO8 (j x : Nat) : Nat := nIf(Nat.blt j 7, jO7 j x, j7 x)
@[expose] noncomputable def jOI8 (j x : Nat) : Nat := nIf(Nat.blt j 7, jOI7 j x, j7I x)
@[expose] noncomputable def j8 (x : Nat) : Nat := trace jO8 jOI8 (ON4W.WC 7) (ON4W.WL 7) x
@[expose] noncomputable def j8I (x : Nat) : Nat := trace jO8 jOI8 (ON4W.WC 15) (ON4W.WL 15) x
@[expose] noncomputable def jF (j x : Nat) : Nat := nIf(Nat.blt j 8, jO8 j x, j8 x)
@[expose] noncomputable def jFI (j x : Nat) : Nat := nIf(Nat.blt j 8, jOI8 j x, j8I x)

@[expose] noncomputable def fastX (N s : Nat) (X P : Nat → Nat) (I slow : Nat → Nat → Nat)
    (j x : Nat) : Nat :=
  strictN (P x) fun p =>
    nIf(bAnd(Nat.blt j s, bAnd(Nat.blt x 245520, Nat.blt p N)), X (I j p), slow j x)

@[expose] noncomputable def xAt (N s m : Nat) (X P : Nat → Nat) (I II O D : Nat → Nat → Nat)
    (i : Nat) : Bool :=
  strictB (X i) fun x => bAnd(Nat.blt x 245520, bAnd(Nat.beq (P x) i, allN s fun j =>
    strictB (I j i) fun a => strictB (II j i) fun b =>
    bAnd(Nat.blt a N, bAnd(Nat.blt b N, bAnd(Nat.beq (I j b) i,
      bIf(Nat.blt j m, Nat.beq (X a) (O j x), Nat.beq a (D j i)))))))

@[expose] noncomputable def pxAt (N : Nat) (X P : Nat → Nat) (x : Nat) : Bool :=
  strictB (P x) fun p => bIf(Nat.blt p N, Nat.beq (X p) x, true)

@[expose] noncomputable def xT (i : Nat) : Nat := tab ON4X.XT i
@[expose] noncomputable def pT (x : Nat) : Nat := tab ON4X.PT x
@[expose] noncomputable def xM (i : Nat) : Nat := tab ON4X.XM i
@[expose] noncomputable def pM (x : Nat) : Nat := tab ON4X.PM x

@[expose] noncomputable def iT (j i : Nat) : Nat := tab ON4X.T (Nat.add (Nat.mul 1152 j) i)
@[expose] noncomputable def iTI (j i : Nat) : Nat := tab ON4X.TI (Nat.add (Nat.mul 1152 j) i)
@[expose] noncomputable def iM (j i : Nat) : Nat := tab ON4X.M (Nat.add (Nat.mul 27120 j) i)
@[expose] noncomputable def iMI (j i : Nat) : Nat := tab ON4X.MI (Nat.add (Nat.mul 27120 j) i)
@[expose] noncomputable def iL (j i : Nat) : Nat := tab ON4X.L (Nat.add (Nat.mul 27120 j) i)
@[expose] noncomputable def iLI (j i : Nat) : Nat := tab ON4X.LI (Nat.add (Nat.mul 27120 j) i)
@[expose] noncomputable def iMc (j i : Nat) : Nat := tab ON4X.Mc (Nat.add (Nat.mul 27120 j) i)
@[expose] noncomputable def iMcI (j i : Nat) : Nat := tab ON4X.McI (Nat.add (Nat.mul 27120 j) i)
@[expose] noncomputable def iLc (j i : Nat) : Nat := tab ON4X.Lc (Nat.add (Nat.mul 27120 j) i)
@[expose] noncomputable def iLcI (j i : Nat) : Nat := tab ON4X.LcI (Nat.add (Nat.mul 27120 j) i)

@[expose] noncomputable def dT (j i : Nat) : Nat :=
  trace iT iTI (ON3W.WC (Nat.add 11 j)) (ON3W.WL (Nat.add 11 j)) i
@[expose] noncomputable def dM (j i : Nat) : Nat :=
  trace iM iMI (ON3W.WC (Nat.add 16 j)) (ON3W.WL (Nat.add 16 j)) i
@[expose] noncomputable def dL (j i : Nat) : Nat :=
  trace iL iLI (ON3W.WC (Nat.add 19 j)) (ON3W.WL (Nat.add 19 j)) i
@[expose] noncomputable def dMc (j i : Nat) : Nat :=
  trace iMc iMcI (ON4W.WC (Nat.sub j 3)) (ON4W.WL (Nat.sub j 3)) i
@[expose] noncomputable def dLc (j i : Nat) : Nat :=
  trace iLc iLcI (ON4W.WC (Nat.sub j 1)) (ON4W.WL (Nat.sub j 1)) i

@[expose] noncomputable def tFX : Nat → Nat → Nat := fastX 1152 8 xT pT iT tF
@[expose] noncomputable def tFIX : Nat → Nat → Nat := fastX 1152 8 xT pT iTI tFI
@[expose] noncomputable def mFX : Nat → Nat → Nat := fastX 27120 5 xM pM iM mF
@[expose] noncomputable def mFIX : Nat → Nat → Nat := fastX 27120 5 xM pM iMI mFI
@[expose] noncomputable def lFX : Nat → Nat → Nat := fastX 27120 4 xM pM iL lF
@[expose] noncomputable def lFIX : Nat → Nat → Nat := fastX 27120 4 xM pM iLI lFI
@[expose] noncomputable def mcFX : Nat → Nat → Nat := fastX 27120 5 xM pM iMc mcF
@[expose] noncomputable def mcFIX : Nat → Nat → Nat := fastX 27120 5 xM pM iMcI mcFI
@[expose] noncomputable def lcFX : Nat → Nat → Nat := fastX 27120 6 xM pM iLc lcF
@[expose] noncomputable def lcFIX : Nat → Nat → Nat := fastX 27120 6 xM pM iLcI lcFI

@[expose] noncomputable def xTAt (i : Nat) : Bool := xAt 1152 8 6 xT pT iT iTI tG dT i

@[expose] noncomputable def xMAt (i : Nat) : Bool :=
  bAnd(xAt 27120 5 3 xM pM iM iMI mG dM i, bAnd(xAt 27120 4 2 xM pM iL iLI lG dL i,
    bAnd(xAt 27120 5 3 xM pM iMc iMcI mcO dMc i, xAt 27120 6 3 xM pM iLc iLcI lcO dLc i)))

@[expose] noncomputable def xMS (s : Nat) : Bool :=
  allN (nat_lit 565) fun d => xMAt (Nat.add (Nat.mul s (nat_lit 565)) d)

@[expose] noncomputable def pxS (s : Nat) : Bool :=
  allN (nat_lit 30690) fun d => strictB (Nat.add (Nat.mul s (nat_lit 30690)) d) fun x =>
    bAnd(pxAt 1152 xT pT x, bAnd(pxAt 27120 xM pM x, bIf(Nat.blt x 1152, xTAt x, true)))

@[expose] noncomputable def mcPTS : Nat → Nat → Nat := lv3 ON4LMc.PTS0 ON4LMc.PTS1 ON4LMc.PTS2
@[expose] noncomputable def mcPOS : Nat → Nat → Nat := lv3 ON4LMc.POS0 ON4LMc.POS1 ON4LMc.POS2
@[expose] noncomputable def mcPAR : Nat → Nat → Nat := lv3 ON4LMc.PAR0 ON4LMc.PAR1 ON4LMc.PAR2
@[expose] noncomputable def mcLAB : Nat → Nat → Nat := lv3 ON4LMc.LAB0 ON4LMc.LAB1 ON4LMc.LAB2
@[expose] noncomputable def mcMr : Nat → Nat := nat3 ON4LMc.M0 ON4LMc.M1 ON4LMc.M2
@[expose] noncomputable def mcIDX (i t : Nat) : Nat := nIf(Nat.beq i 0, t, Nat.add 3 t)
@[expose] noncomputable def mcLEN : Nat → Nat := nat3 5 2 0

@[expose] noncomputable def lcPTS : Nat → Nat → Nat := lv3 ON4LLc.PTS0 ON4LLc.PTS1 ON4LLc.PTS2
@[expose] noncomputable def lcPOS : Nat → Nat → Nat := lv3 ON4LLc.POS0 ON4LLc.POS1 ON4LLc.POS2
@[expose] noncomputable def lcPAR : Nat → Nat → Nat := lv3 ON4LLc.PAR0 ON4LLc.PAR1 ON4LLc.PAR2
@[expose] noncomputable def lcLAB : Nat → Nat → Nat := lv3 ON4LLc.LAB0 ON4LLc.LAB1 ON4LLc.LAB2
@[expose] noncomputable def lcMr : Nat → Nat := nat3 ON4LLc.M0 ON4LLc.M1 ON4LLc.M2
@[expose] noncomputable def lcIDX (i t : Nat) : Nat := nIf(Nat.beq i 0, t, Nat.add 3 t)
@[expose] noncomputable def lcLEN : Nat → Nat := nat3 6 3 0

@[expose] noncomputable def ptC (i s : Nat) : Bool :=
  bAnd(cbPtRange 245520 (mcMr i) (Nat.mul 2 (mcLEN i)) (stepX mcFX mcFIX (mcIDX i) (mcLEN i))
      (mcPTS i) (mcPOS i) (mcPAR i) (mcLAB i) (Nat.mul s 16) 16,
    cbPtRange 245520 (lcMr i) (Nat.mul 2 (lcLEN i)) (stepX lcFX lcFIX (lcIDX i) (lcLEN i))
      (lcPTS i) (lcPOS i) (lcPAR i) (lcLAB i) (Nat.mul s 16) 16)

@[expose] noncomputable def ptC0 (s : Nat) : Bool := ptC 0 s
@[expose] noncomputable def ptC1 (s : Nat) : Bool := ptC 1 s
@[expose] noncomputable def ptC2 (s : Nat) : Bool := ptC 2 s

@[expose] noncomputable def posCS (u : Nat) : Bool :=
  strictB (Nat.mod u 8) fun s => strictB (Nat.div u 8) fun i =>
  allN (nat_lit 30690) fun d => strictB (Nat.add (Nat.mul s (nat_lit 30690)) d) fun z =>
    bAnd(cbPos 245520 (mcMr i) (mcPTS i) (mcPOS i) z, cbPos 245520 (lcMr i) (lcPTS i) (lcPOS i) z)

@[expose] noncomputable def schC (c i s : Nat) : Bool :=
  allN (nat_lit 16) fun d => strictB (Nat.add (Nat.mul s (nat_lit 16)) d) fun h =>
  bIf(Nat.beq c 0, bIf(Nat.blt h (tMr i), allN (Nat.mul 2 (tLEN i)) fun j =>
      schK (fun i => stepX tFX tFIX (tIDX i) (tLEN i)) (fun i => invX tFX tFIX (tIDX i) (tLEN i))
        tPTS tPOS tPAR tLAB tMr bB i h j, true),
  bIf(Nat.beq c 1, bIf(Nat.blt h (mMr i), allN (Nat.mul 2 (mLEN i)) fun j =>
      schK (fun i => stepX mFX mFIX (mIDX i) (mLEN i)) (fun i => invX mFX mFIX (mIDX i) (mLEN i))
        mPTS mPOS mPAR mLAB mMr bB i h j, true),
  bIf(Nat.beq c 2, bIf(Nat.blt h (lMr i), allN (Nat.mul 2 (lLEN i)) fun j =>
      schK (fun i => stepX lFX lFIX (lIDX i) (lLEN i)) (fun i => invX lFX lFIX (lIDX i) (lLEN i))
        lPTS lPOS lPAR lLAB lMr bB i h j, true),
  bIf(Nat.beq c 3, bIf(Nat.blt h (mcMr i), allN (Nat.mul 2 (mcLEN i)) fun j =>
      schK (fun i => stepX mcFX mcFIX (mcIDX i) (mcLEN i))
        (fun i => invX mcFX mcFIX (mcIDX i) (mcLEN i)) mcPTS mcPOS mcPAR mcLAB mcMr bB i h j, true),
    bIf(Nat.blt h (lcMr i), allN (Nat.mul 2 (lcLEN i)) fun j =>
      schK (fun i => stepX lcFX lcFIX (lcIDX i) (lcLEN i))
        (fun i => invX lcFX lcFIX (lcIDX i) (lcLEN i)) lcPTS lcPOS lcPAR lcLAB lcMr bB i h j,
      true)))))

@[expose] noncomputable def sch0 (s : Nat) : Bool :=
  allN 5 fun c => schC c 0 s

@[expose] noncomputable def sch1 (s : Nat) : Bool :=
  allN 5 fun c => schC c 1 s

@[expose] noncomputable def sch2 (s : Nat) : Bool :=
  allN 5 fun c => schC c 2 s

@[expose] noncomputable def jPTS : Nat → Nat → Nat := lv3 ON4J.P0 ON4J.P1 ON4J.P2
@[expose] noncomputable def jPOS : Nat → Nat → Nat := lv3 ON4J.Q0 ON4J.Q1 ON4J.Q2
@[expose] noncomputable def jPAR : Nat → Nat → Nat := lv3 ON4J.R0 ON4J.R1 ON4J.R2
@[expose] noncomputable def jLAB : Nat → Nat → Nat := lv3 ON4J.L0 ON4J.L1 ON4J.L2
@[expose] noncomputable def jIDX (i t : Nat) : Nat :=
  nIf(Nat.beq i 0, t, nIf(Nat.beq i 1, nIf(Nat.blt t 2, t, Nat.add 4 t), Nat.add 7 t))
@[expose] noncomputable def jLEN : Nat → Nat := nat3 9 5 2
@[expose] noncomputable def jT : Nat → Nat := nat3 245520 52136 36

@[expose] noncomputable def treeS (i s : Nat) : Bool :=
  allN (nat_lit 2048) fun d => strictB (Nat.add (Nat.mul s (nat_lit 2048)) d) fun k =>
    bIf(Nat.blt k (jT i), treePt 245520 (Nat.mul 2 (jLEN i)) (stepX jF jFI (jIDX i) (jLEN i))
      (jPTS i) (jPOS i) (jPAR i) (jLAB i) (bB i) k, true)

@[expose] noncomputable def tree0 (s : Nat) : Bool := treeS 0 s
@[expose] noncomputable def tree1 (s : Nat) : Bool := treeS 1 s
@[expose] noncomputable def tree2 (s : Nat) : Bool :=
  treePt 245520 (Nat.mul 2 (jLEN 2)) (stepX jF jFI (jIDX 2) (jLEN 2)) (jPTS 2) (jPOS 2) (jPAR 2)
    (jLAB 2) (bB 2) s

@[expose] noncomputable def headsOK : Bool :=
  allN 3 fun i => bAnd(idxOK mcFX 5 bB i (mcIDX i) (mcLEN i), bAnd(idxOK lcFX 6 bB i (lcIDX i) (lcLEN i),
    bAnd(idxOK jF 9 bB i (jIDX i) (jLEN i),
    bAnd(cbHead 245520 (mcMr i) (bB i) (mcPTS i) (mcPAR i) (mcLAB i),
      cbHead 245520 (lcMr i) (bB i) (lcPTS i) (lcPAR i) (lcLAB i)))))

end CertificateChecks.KernelSpor.ON4K

end
