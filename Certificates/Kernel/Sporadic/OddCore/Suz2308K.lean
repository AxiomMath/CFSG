module

public import Certificates.Kernel.Sporadic.OddCore.Suz2308D
public import Certificates.Kernel.Sporadic.OddCore.Suz2308C
public import Certificates.Kernel.Sporadic.OddCore.SuzCert
public import Certificates.Kernel.Sporadic.OddCore.SuzCenter
public import Certificates.Kernel.Sporadic.OddCore.SuzLocal
public import Certificates.Data.Kernel.Spor.RowWord
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.Kernel.Spor.Mathieu
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.S2308

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Row CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.Raw CFSG.KS.Mathieu CertificateChecks.KernelSpor
@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def rl (F : Nat → Nat) (o x : Nat) : Nat := rg 15 (mask 15) F o x

@[expose] noncomputable def o2 (f g : Nat → Nat) (x : Nat) : Nat := strictN (g x) f

@[expose] noncomputable def itr (f : Nat → Nat) (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => strictN ih f) k

@[expose] noncomputable def ofs (j : Nat) : Nat := Nat.mul 715 j
@[expose] noncomputable def ocs (h : Nat) : Nat := Nat.mul 715 (Nat.add h 2)
@[expose] noncomputable def cgk (k x : Nat) : Nat := rl SuzCertT.F (ofs k) x
@[expose] noncomputable def ci (k x : Nat) : Nat := rl SuzCertI (ofs k) x
@[expose] noncomputable def cf (r x : Nat) : Nat := rl SuzCenR (ofs r) x
@[expose] noncomputable def zx (x : Nat) : Nat := cf 1 x
@[expose] noncomputable def ld (i : Nat) : Nat := pg 15 (mask 15) (SuzLocT.F 0) i

@[expose] noncomputable def rwG (f g : Nat → Nat → Nat) (wd : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (ih x) (fun y => Int.rec (motive := fun _ => Nat)
      (fun k => f (Nat.sub k (nat_lit 1)) y) (fun k => g k y) z)) wd

@[expose] noncomputable def wpC (wd : List Int) (x : Nat) : Nat :=
  rwordPt 15 (mask 15) SuzCertT.F SuzCertI ofs wd x

@[expose] def suzRowW : List (List Int) :=
  [[-7, 9, 6], [-6, -11, 12, 6], [9, -8, 6, 11, -8, 5], [-6, 10, -12, -11, 8, -6, 7, -6],
    [-6, -5, -9, -6, 7, -10, 5, 12], [-6, 10, -5, 8, -7, 5, 8, -11]]

@[expose] def suzTxW : List (List Int) :=
  [[-5, 6, -10, 11, 10, 5, 6], [-12, -5, 9, 6, -10, -6, 11], [-5, 11, 6, 12, 10, -11, 6],
    [-6, 9, 6, -9, 6, 6, 8, 11], [-5, -8, -5, 10, 7, 6, -11, 7]]

@[expose] def suzInvW (wd : List Int) : List Int := (wd.map Int.neg).reverse

@[expose] noncomputable def fy (j x : Nat) : Nat :=
  nIf(Nat.blt j 8, cgk (Nat.add j 4) x, wpC (suzRowW.getD (Nat.sub j 8) []) x)
@[expose] noncomputable def fyi (j x : Nat) : Nat :=
  nIf(Nat.blt j 8, ci (Nat.add j 4) x, wpC (suzInvW (suzRowW.getD (Nat.sub j 8) [])) x)

@[expose] noncomputable def tx (a x : Nat) : Nat := wpC (suzTxW.getD a []) x

@[expose] noncomputable def wpS (wd : List Int) (x : Nat) : Nat :=
  rwordPt 15 (mask 15) SuzCertT.F SuzCertI ocs wd x

@[expose] def fusW : List Int := [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2]

@[expose] def suzC5W : List Int := [11, 5, -8, 5, -11]
@[expose] def suzC8W : List Int := [6, -8]
@[expose] def suzGW : List Int := [-2, -5, -1, 2, 1, 5, 2]

@[expose] noncomputable def gx (x : Nat) : Nat := wpC suzGW x
@[expose] noncomputable def gxi (x : Nat) : Nat := wpC (suzInvW suzGW) x

theorem suzLvl : allN 6 (fun p => bAnd(allN 6 (fun k =>
      bAnd(Nat.beq (fy (Nat.add 8 k) p) (rwG fy fyi (localDerivs.getD (Nat.add 8 k) []) p),
        Nat.beq (fy (Nat.add 8 k) (fyi (Nat.add 8 k) p)) p)),
    allN 5 (fun a => Nat.beq (tx a p) (rwG fy fyi (sylowQuotWords.getD a []) p)))) = true := by
  quickRfl

@[expose] noncomputable def zBP (x : Nat) : Bool :=
  bAnd(Nat.beq (itr zx 3 x) x,
    allN 8 (fun j => Nat.beq (o2 (cgk (Nat.add j 4)) (o2 zx (ci (Nat.add j 4))) x)
      (nIf(Nat.beq (nget S2308W (Nat.add 82 j)) 0, zx x, o2 zx zx x))))

theorem zbase : allN 6 zBP = true := by quickRfl

theorem zpts : bAnd(Nat.beq (zx 0) 0, bAnd(notB (Nat.beq (zx (nget S2308W 0)) (nget S2308W 0)),
    Nat.blt (nget S2308W 0) 22880)) = true := by
  quickRfl

theorem rst : bAnd(allN 14 (fun j => allN 280 (fun i =>
      Nat.beq (fy j (ld i)) (ld (pg 9 (mask 9) (SuzLocR (Nat.add 8 j)) i)))),
    bAnd(allN 5 (fun a => allN 280 (fun i =>
      Nat.beq (tx a (ld i)) (ld (pg 9 (mask 9) (S2308CE.G a) i)))),
    bAnd(allN 280 (fun i => Nat.beq (cf 3 (ld i)) (ld (pg 9 (mask 9) (SuzCenC 3) i))),
    bAnd(allN 280 (fun i => bAnd(notB (Nat.beq (ld i) 0), Nat.beq (zx (ld i)) (ld i))),
    bAnd(allN 8 (fun k => Nat.beq (SuzLocR k) (SuzLocR (Nat.add 8 k))),
    bAnd(allN 14 (fun j => Nat.beq (S2308LC.S j) (SuzLocR (Nat.add 8 j))),
      allN 4 (fun t => Nat.beq (nget [0, 1, 2, 3] t) (pg 9 (mask 9) S2308LC.BP t)))))))) =
    true := by quickRfl

theorem pen : bAnd(szOK 280 9, bAnd(allN 5 (fun a => canonK 280 9 (mask 9) (280 * 9) (S2308CE.G a)),
    bAnd(Nat.beq S2308CE.k 5, bAnd(Nat.beq S2308CE.cnt 729,
    bAnd(canonK 280 9 (mask 9) (280 * 9) (SuzCenC 3),
    bAnd(notB (Nat.beq (SuzCenC 3) (pidn 280 9)),
      penumHdK (pidn 280 9) S2308CE.cnt 729 S2308CE.T S2308CE.PL)))))) = true := by quickRfl

@[expose] noncomputable def s23Pt (n w m : Nat) (conj : Bool) (G GI : Nat → Nat)
    (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
    strictB (parOf PL i) (fun p => strictB (labOf PL i) (fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l k, bAnd(Nat.beq (r32 POS (Nat.add (Nat.mul p k) l)) i,
      bIf(Nat.blt (Nat.succ i) cnt,
        lexLtK p l (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)), true))))))),
  bAnd(allN k (fun j => strictB (r32 POS (Nat.add (Nat.mul i k) j)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (T q) (stepK n w m conj G GI j t),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL q) (labOf PL q), false, true)))))),
  strictB (r32 SRT i) (fun s => bAnd(Nat.blt s cnt, bAnd(Nat.beq (r32 SRI s) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T s) (T (r32 SRT (Nat.succ i))), true)))))))

@[expose] noncomputable def s23Sl (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i S2308CE.cnt, s23Pt 280 9 (mask 9) false S2308CE.G S2308CE.GI 5 S2308CE.cnt
      S2308CE.T S2308CE.PL S2308CE.POS S2308CE.SRT S2308CE.SRI i, true)))

theorem pts0 : s23Sl 0 365 = true := by quickRfl
theorem pts1 : s23Sl 365 365 = true := by quickRfl

@[expose] noncomputable def escP (k : Nat) : Bool :=
  strictB (S2308CE.T k) (fun t =>
    bIf(allN 5 (fun a => Nat.beq (pcomp 280 9 (mask 9) (S2308CE.G a) t)
        (pcomp 280 9 (mask 9) t (S2308CE.G a))),
      bIf(Nat.beq t (pidn 280 9), true, bIf(Nat.beq t (SuzCenC 3), true,
        Nat.beq t (pcomp 280 9 (mask 9) (SuzCenC 3) (SuzCenC 3)))), true))

theorem esc : allN 729 escP = true := by quickRfl

@[expose] noncomputable def cenP (x : Nat) : Bool :=
  bAnd(Nat.beq (cf 0 x) x, bAnd(Nat.beq (zx x) (cf 5 (cf 8 x)), bAnd(Nat.beq (cf 2 x) (cf 1 (zx x)),
  bAnd(Nat.beq (cf 4 x) (cf 3 (zx x)), bAnd(Nat.beq (cf 5 x) (cf 4 (zx x)),
  bAnd(Nat.beq (cf 6 x) (cf 3 (cf 3 x)), bAnd(Nat.beq (cf 7 x) (cf 6 (zx x)),
  bAnd(Nat.beq (cf 8 x) (wpC suzC8W (cf 5 (wpC suzC8W x))), Nat.beq (cf 5 x) (wpC suzC5W x)))))))))

@[expose] noncomputable def s23cV (x : Nat) : Nat :=
  nIf(cenP x, Nat.add (nIf(Nat.beq (cf 3 x) x, 1, 0)) (Nat.add (nIf(Nat.beq (cf 4 x) x, 8192, 0))
    (nIf(bAnd(notB (Nat.beq x 0), Nat.beq (zx x) x), 67108864, 0))), 549755813888)

@[expose] noncomputable def s23cS (q : Nat) : Nat :=
  foldN 5720 (fun d s => Nat.add s (s23cV (Nat.add (Nat.mul 5720 q) d))) 0

@[expose] noncomputable def s23cB (q N : Nat) : Bool := Nat.beq (s23cS q) N

theorem cq0 : s23cB 0 4899061774 = true := by quickRfl
theorem cq1 : s23cB 1 4831895559 = true := by quickRfl
theorem cq2 : s23cB 2 4093706248 = true := by quickRfl
theorem cq3 : s23cB 3 4966129673 = true := by quickRfl

@[expose] noncomputable def cenBP (x : Nat) : Bool :=
  bAnd(Nat.beq (o2 (cf 1) (cf 1) x) (cf 2 x), bAnd(Nat.beq (o2 (cf 3) (cf 3) x) (cf 6 x),
  bAnd(Nat.beq (o2 (cf 4) (cf 4) x) (cf 8 x), bAnd(Nat.beq (o2 (cf 5) (cf 5) x) (cf 7 x),
  bAnd(Nat.beq (o2 (cf 3) zx x) (o2 zx (cf 3) x),
  bAnd(allN 5 (fun a => bAnd(Nat.beq (o2 (cf 3) (tx a) x) (o2 (tx a) (cf 3) x),
    Nat.beq (o2 zx (tx a) x) (o2 (tx a) zx x))),
    bAnd(Nat.beq (itr (cf 3) 3 x) x, Nat.beq (cf 8 x) (cf 7 (zx x)))))))))

theorem cenbase : allN 6 cenBP = true := by quickRfl

theorem sbase : allN 6 (fun x => bAnd(Nat.beq (zx x) (itr (wpS zWord) 7 x),
    bAnd(Nat.beq (gx x) (wpC fusW x), Nat.beq (cf 3 x) (tx 1 x)))) = true := by quickRfl

theorem cdist : allN 9 (fun r => allN 9 (fun r' => bIf(Nat.blt r r',
    bAnd(Nat.blt (nget S2308W (Nat.add 1 (Nat.add (Nat.mul 9 r) r'))) 22880,
      notB (Nat.beq (cf r (nget S2308W (Nat.add 1 (Nat.add (Nat.mul 9 r) r'))))
        (cf r' (nget S2308W (Nat.add 1 (Nat.add (Nat.mul 9 r) r')))))), true))) = true := by
  quickRfl

theorem gzbase : bAnd(Nat.beq (gx 0) 95, allN 6 (fun x => bAnd(Nat.beq (o2 gx (o2 zx gxi) x) (cf 5 x),
    Nat.beq (gx (gxi x)) x))) = true := by quickRfl

@[expose] noncomputable def nwN (k : Nat) : List Nat := (normWords.getD k []).map fun l => l.toNat - 1

@[expose] noncomputable def nwK (k : Nat) : Nat := wordTabK 280 9 (mask 9) (pidn 280 9) SuzLocR (nwN k)
@[expose] noncomputable def nwiK (k : Nat) : Nat :=
  wordTabK 280 9 (mask 9) (pidn 280 9) SuzLocRI (nwN k).reverse

@[expose] noncomputable def ncK (k : Nat) : Nat :=
  pcomp 280 9 (mask 9) (nwK k) (pcomp 280 9 (mask 9) (SuzCenC 3) (nwiK k))

theorem nw : bAnd(canonK 280 9 (mask 9) (280 * 9) (pidn 280 9),
    bAnd(allN 8 (fun k => bAnd(canonK 280 9 (mask 9) (280 * 9) (SuzLocR k),
      canonK 280 9 (mask 9) (280 * 9) (SuzLocRI k))),
    bAnd(allN 39 (fun k => bAnd(allN (lenN (nwN k)) (fun i => Nat.blt (nget (nwN k) i) 8),
      invEqK 280 9 (mask 9) (280 * 9) (nwK k) (nwiK k))),
    allN 39 (fun k => strictB (ncK k) (fun a => allN 39 (fun k' => bIf(Nat.blt k k',
      strictB (ncK k') (fun b => bAnd(notB (Nat.beq a b),
        notB (Nat.beq a (pcomp 280 9 (mask 9) b b)))), true))))))) = true := by quickRfl

end CertificateChecks.KernelSpor.OddCore.S2308

end
