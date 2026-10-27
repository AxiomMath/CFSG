module

public import Certificates.Kernel.J3Coset.Data
public import Certificates.Data.Kernel.J3Coset

public section

namespace CertificateChecks.KernelJ3C

open CFSG.KC.Enum CFSG.KC.J3C CFSG.KD.J3C

@[expose] noncomputable def tb (c y : Nat) : Nat :=
  e16 TT (Nat.add (Nat.mul (nIf(Nat.beq c (nat_lit 1), nat_lit 0, c)) (nat_lit 25856)) y)

@[expose] noncomputable def invC (c : Nat) : Nat :=
  if c = 0 then 1 else if c = 1 then 0 else if c = 2 then 3 else if c = 3 then 2 else c

@[expose] noncomputable def invW (w : List Nat) : List Nat := (w.map invC).reverse

@[expose] noncomputable def rep (k : Nat) (w : List Nat) : List Nat := (List.replicate k w).flatten

@[expose] noncomputable def fgw (f j : Nat) : List Nat :=
  if f = 0 then (if j = 0 then [0] else [2])
  else if f = 1 then (if j = 0 then [4] else [5])
  else if f < 21 then (if j = 0 then [4] else if j = 1 then [5] else gws.getD (f - 2) [])
  else if j = 0 then [6] else if j = 1 then [7]
  else if j = 2 then gws.getD (f - 21) [] ++ [6] ++ invW (gws.getD (f - 21) [])
  else gws.getD (f - 21) [] ++ [7] ++ invW (gws.getD (f - 21) [])

@[expose] noncomputable def rf (f r : Nat) : Nat := if f = 1 then roots.getD r 0 else 0

@[expose] noncomputable def slice (f : Nat → Bool) (s : Nat) : Bool :=
  strictB (Nat.mul s (nat_lit 323)) fun lo => allN (nat_lit 323) fun t => f (Nat.add lo t)

@[expose] noncomputable def permPt (y : Nat) : Bool :=
  bAnd(Nat.blt (tb 0 y) (nat_lit 25840), bAnd(Nat.beq (tb 0 (tb 0 y)) y,
  bAnd(Nat.blt (tb 2 y) (nat_lit 25840), bAnd(Nat.blt (tb 3 y) (nat_lit 25840),
  bAnd(Nat.beq (tb 3 (tb 2 y)) y, bAnd(Nat.beq (tb 2 (tb 3 y)) y,
  bAnd(Nat.blt (tb 8 y) (nat_lit 25840), bAnd(Nat.blt (tb 9 y) (nat_lit 25840),
  bAnd(Nat.beq (tb 9 (tb 8 y)) y, Nat.beq (tb 8 (tb 9 y)) y)))))))))

@[expose] noncomputable def relPtJ (y : Nat) : Bool := relPt tb rels y

@[expose] noncomputable def kPt (y : Nat) : Bool :=
  bAnd(Nat.beq (tb 4 y) (wv tb wK1 y), Nat.beq (tb 5 y) (wv tb wK2 y))

@[expose] noncomputable def pPt (y : Nat) : Bool :=
  bAnd(Nat.beq (tb 6 y) (wv tb wP1 y), Nat.beq (tb 7 y) (wv tb wP2 y))

@[expose] noncomputable def sPt (y : Nat) : Bool :=
  bAnd(Nat.beq (tb 8 (tb 0 y)) (wv tb phiA (tb 8 y)), Nat.beq (tb 8 (tb 2 y)) (wv tb phiB (tb 8 y)))

@[expose] noncomputable def permSl (s : Nat) : Bool := slice permPt s

@[expose] noncomputable def relSl (s : Nat) : Bool := slice relPtJ s

@[expose] noncomputable def kSl (s : Nat) : Bool := slice kPt s

@[expose] noncomputable def pSl (s : Nat) : Bool := slice pPt s

@[expose] noncomputable def sSl (s : Nat) : Bool := slice sPt s

@[expose] noncomputable def forChk (f : Nat) : Bool :=
  allN (nat_lit 25840) fun p => fOK (nat_lit 25840)
    (fun q => e64 FT (Nat.add (Nat.mul f (nat_lit 25856)) q)) (fun j q => wv tb (fgw f j) q)
    (rf f) p

@[expose] noncomputable def codesIn (c d : Nat) (w : List Nat) : Bool := w.all fun x => x == c || x == d

@[expose] noncomputable def codesAB (w : List Nat) : Bool := w.all fun x => x < 4

@[expose] noncomputable def fixChk : Bool :=
  tb 4 0 == 0 && tb 5 0 == 0 && tb 6 0 == 0 && tb 7 0 == 0 && tb 8 0 == 0 && beta0 == tb 2 0 &&
  codesAB wK1 && codesAB wK2 && codesIn 4 5 wP1 && codesIn 4 5 wP2 && codesAB phiA &&
  codesAB phiB && rels.all codesAB && sortedB roots && roots.length == 20 &&
  roots.head? == some 0 && gws.length == 19 &&
  (List.range 19).all fun i => codesAB (gws.getD i []) &&
    wv tb (gws.getD i []) 0 == roots.getD (i + 1) 0

@[expose] noncomputable def qChk : Bool :=
  sortedB (Qr.map Prod.fst) && Qr.length == 243 && memB (maskOf Qr) beta0 &&
  Qr.all (fun r => codesIn 6 7 r.2 && wv tb r.2 beta0 == r.1 && memB (maskOf Qr) (tb 6 r.1) &&
    memB (maskOf Qr) (tb 7 r.1)) &&
  baseEq tb beta0 (rep ordP1 [6]) [] && baseEq tb beta0 (rep ordP2 [7]) []

@[expose] noncomputable def oChk : Bool :=
  sortedB (Oc.flatten.map Prod.fst) && Oc.flatten.length == 1944 &&
  Oc.flatten.all (fun r => codesIn 4 5 r.2.1 && wv tb r.2.1 beta0 == r.1)

@[expose] noncomputable def pw (w : List Bool) : List Nat := w.map fun b => if b then 7 else 6

@[expose] noncomputable def ldChk : Bool :=
  codesIn 6 7 cw1 && codesIn 6 7 cw2 &&
  baseEq tb beta0 ([5, 6] ++ rep 7 [5]) cw1 && baseEq tb beta0 ([5, 7] ++ rep 7 [5]) cw2 &&
  baseEq tb beta0 (rep 8 [5]) [] && !(wv tb (rep 4 [5]) beta0 == beta0) &&
  !(wv tb [6, 7] beta0 == wv tb [7, 6] beta0) &&
  sortedB (Zr.map Prod.fst) && Zr.length == 9 &&
  Zr.all (fun r => codesIn 6 7 r.2 && wv tb r.2 beta0 == r.1 &&
    baseEq tb beta0 (r.2 ++ [6]) ([6] ++ r.2) && baseEq tb beta0 (r.2 ++ [7]) ([7] ++ r.2) &&
    baseEq tb beta0 (rep 3 r.2) [] &&
    (r.1 == beta0 || (!(wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 == beta0) &&
      !(wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 == r.1) &&
      !(wv tb ([5] ++ r.2 ++ rep 7 [5]) beta0 == wv tb (r.2 ++ r.2) beta0)))) &&
  Qr.all (fun r => memB (maskOf Zr) r.1 || !(wv tb (r.2 ++ [6]) beta0 == wv tb ([6] ++ r.2) beta0) ||
    !(wv tb (r.2 ++ [7]) beta0 == wv tb ([7] ++ r.2) beta0)) &&
  zc.length == 9 && (Zr.zip zc).all (fun r => baseEq tb beta0 ([5] ++ r.1.2 ++ rep 7 [5])
    (Zr.getD r.2 (0, [])).2) &&
  zk.length == 7 && ((List.range' 1 7).zip zk).all (fun r =>
    !(wv tb (rep r.1 [5] ++ (Zr.getD r.2 (0, [])).2) beta0 ==
      wv tb ((Zr.getD r.2 (0, [])).2 ++ rep r.1 [5]) beta0)) &&
  baseEq tb beta0 ([5, 5, 6] ++ rep 6 [5]) (pw sw1) && baseEq tb beta0 ([5, 5, 7] ++ rep 6 [5]) (pw sw2)

@[expose] noncomputable def covChk : Bool :=
  baseEq tb beta0 (rep 3 xW) [] && !(baseEq tb beta0 xW []) &&
  baseEq tb beta0 (d1W ++ xW) (xW ++ d1W) && baseEq tb beta0 (d2W ++ xW) (xW ++ d2W) &&
  baseEq tb beta0 (gW ++ xW) (invW xW ++ gW) &&
  baseEq tb beta0 (rep 2 d1W) [] && baseEq tb beta0 (rep 4 d2W) [] &&
  baseEq tb beta0 (rep 5 (d1W ++ d2W)) [] && baseEq tb beta0 (rep 5 (d1W ++ rep 2 d2W)) [] &&
  uW == d1W ++ d2W ++ d1W ++ d2W ++ d2W ++ d1W ++ d2W ++ d2W ++ d2W &&
  baseEq tb beta0 (rep 3 uW) [] && !(baseEq tb beta0 uW []) && !(baseEq tb beta0 uW xW) &&
  !(baseEq tb beta0 uW (rep 2 xW)) && baseEq tb beta0 (d1W ++ uW) (invW uW ++ d1W) &&
  [xW, d1W, d2W, gW].all codesAB

@[expose] noncomputable def outChk : Bool :=
  codesIn 6 7 phiW1 && codesIn 6 7 phiW2 &&
  wv tb [8, 6, 9] beta0 == wv tb phiW1 beta0 && wv tb [8, 7, 9] beta0 == wv tb phiW2 beta0 &&
  !(memB (maskOf Oc.flatten) (tb 8 beta0)) &&
  Zr.all (fun r => r.1 == beta0 || (List.range' 1 7).all fun k =>
    !(baseEq tb beta0 (rep k [5] ++ r.2) (r.2 ++ rep k [5])))

@[expose] noncomputable def recOK (r : Nat × List Nat × Nat × Nat × List Nat × List Nat) : Bool :=
  if r.2.2.1 == 0 then
    !(wv tb r.2.1 (tb 8 (wv tb r.2.1 (tb 8 r.2.2.2.1))) == r.2.2.2.1)
  else
    wv tb r.2.1 (tb 8 r.2.2.2.1) == beta0 && codesIn 6 7 r.2.2.2.2.1 &&
    baseEq tb beta0 (rep 9 r.2.2.2.2.1) [] && r.2.2.2.2.2.length == 243 &&
    (Qr.zip r.2.2.2.2.2).all fun qj =>
      if qj.2 < 9 then wv tb (rep qj.2 r.2.2.2.2.1) beta0 == qj.1.1
      else !(wv tb r.2.1 (tb 8 (wv tb qj.1.2 r.2.2.2.1)) == qj.1.1)

@[expose] noncomputable def recChk (c : Nat) : Bool := (Oc.getD c []).all recOK

end CertificateChecks.KernelJ3C

end
