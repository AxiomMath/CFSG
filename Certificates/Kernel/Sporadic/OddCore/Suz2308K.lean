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

@[expose] noncomputable def allR (lo len : Nat) (f : Nat → Bool) : Bool :=
  allN len (fun d => f (Nat.add lo d))

@[expose] noncomputable def rl (F : Nat → Nat) (o x : Nat) : Nat := rg 15 (mask 15) F o x

@[expose] noncomputable def o2 (f g : Nat → Nat) (x : Nat) : Nat := strictN (g x) f

@[expose] noncomputable def itr (f : Nat → Nat) (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => strictN ih f) k

@[expose] noncomputable def ofs (j : Nat) : Nat := Nat.mul 715 j
@[expose] noncomputable def ocs (h : Nat) : Nat := Nat.mul 715 (Nat.add h 2)
@[expose] noncomputable def fx (j x : Nat) : Nat := rl S2308FX (ofs j) x
@[expose] noncomputable def tx (a x : Nat) : Nat := rl S2308TX (ofs a) x
@[expose] noncomputable def wx (x : Nat) : Nat := rl S2308WX 0 x
@[expose] noncomputable def zx (x : Nat) : Nat := rl S2308ZX 0 x
@[expose] noncomputable def gx (x : Nat) : Nat := rl S2308GX 0 x
@[expose] noncomputable def gxi (x : Nat) : Nat := rl S2308GXI 0 x
@[expose] noncomputable def cgk (k x : Nat) : Nat := rl SuzCertT.F (ofs k) x
@[expose] noncomputable def ci (k x : Nat) : Nat := rl SuzCertI (ofs k) x
@[expose] noncomputable def cf (r x : Nat) : Nat := rl SuzCenR (ofs r) x
@[expose] noncomputable def ld (i : Nat) : Nat := pg 15 (mask 15) (SuzLocT.F 0) i

@[expose] noncomputable def wpF (wd : List Int) (x : Nat) : Nat :=
  rwordPt 15 (mask 15) S2308FX S2308FXI ofs wd x

@[expose] noncomputable def wpC (wd : List Int) (x : Nat) : Nat :=
  rwordPt 15 (mask 15) SuzCertT.F SuzCertI ofs wd x

@[expose] noncomputable def wpS (wd : List Int) (x : Nat) : Nat :=
  rwordPt 15 (mask 15) SuzCertT.F SuzCertI ocs wd x

@[expose] def fusW : List Int := [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2]

@[expose] noncomputable def qtr (f : Nat → Bool) (q : Nat) : Bool := allR (Nat.mul 5720 q) 5720 f

theorem fbase : allN 8 (fun j => allN 715 (fun r => Nat.beq (S2308FX (Nat.add (ofs j) r))
    (SuzCertT.F (Nat.add (ofs (Nat.add j 4)) r)))) = true := by quickRfl

theorem fperm : allN 14 (fun j => rpermK 22880 15 (mask 15) S2308FX (ofs j) S2308FXI (ofs j)) =
    true := by quickRfl

@[expose] noncomputable def fdP (k x : Nat) : Bool :=
  Nat.beq (fx (Nat.add 8 k) x) (wpF (localDerivs.getD (Nat.add 8 k) []) x)

theorem fd0 : allN 22880 (fdP 0) = true := by quickRfl
theorem fd1 : allN 22880 (fdP 1) = true := by quickRfl
theorem fd2 : allN 22880 (fdP 2) = true := by quickRfl
theorem fd3 : allN 22880 (fdP 3) = true := by quickRfl
theorem fd4 : allN 22880 (fdP 4) = true := by quickRfl
theorem fd5 : allN 22880 (fdP 5) = true := by quickRfl

@[expose] noncomputable def twP (a x : Nat) : Bool :=
  Nat.beq (tx a x) (wpF (sylowQuotWords.getD a []) x)

theorem tw0q0 : qtr (twP 0) 0 = true := by quickRfl
theorem tw0q1 : qtr (twP 0) 1 = true := by quickRfl
theorem tw0q2 : qtr (twP 0) 2 = true := by quickRfl
theorem tw0q3 : qtr (twP 0) 3 = true := by quickRfl
theorem tw1q0 : qtr (twP 1) 0 = true := by quickRfl
theorem tw1q1 : qtr (twP 1) 1 = true := by quickRfl
theorem tw1q2 : qtr (twP 1) 2 = true := by quickRfl
theorem tw1q3 : qtr (twP 1) 3 = true := by quickRfl
theorem tw2q0 : qtr (twP 2) 0 = true := by quickRfl
theorem tw2q1 : qtr (twP 2) 1 = true := by quickRfl
theorem tw2q2 : qtr (twP 2) 2 = true := by quickRfl
theorem tw2q3 : qtr (twP 2) 3 = true := by quickRfl
theorem tw3q0 : qtr (twP 3) 0 = true := by quickRfl
theorem tw3q1 : qtr (twP 3) 1 = true := by quickRfl
theorem tw3q2 : qtr (twP 3) 2 = true := by quickRfl
theorem tw3q3 : qtr (twP 3) 3 = true := by quickRfl
theorem tw4q0 : qtr (twP 4) 0 = true := by quickRfl
theorem tw4q1 : qtr (twP 4) 1 = true := by quickRfl
theorem tw4q2 : qtr (twP 4) 2 = true := by quickRfl
theorem tw4q3 : qtr (twP 4) 3 = true := by quickRfl

@[expose] noncomputable def zP (x : Nat) : Bool :=
  bAnd(Nat.beq (wx x) (wpS zWord x), bAnd(Nat.beq (zx x) (itr wx 7 x),
  bAnd(Nat.beq (itr zx 3 x) x,
    allN 8 (fun j => Nat.beq (o2 (cgk (Nat.add j 4)) (o2 zx (ci (Nat.add j 4))) x)
      (nIf(Nat.beq (nget S2308W (Nat.add 82 j)) 0, zx x, o2 zx zx x))))))

theorem zq0 : qtr zP 0 = true := by quickRfl
theorem zq1 : qtr zP 1 = true := by quickRfl
theorem zq2 : qtr zP 2 = true := by quickRfl
theorem zq3 : qtr zP 3 = true := by quickRfl

@[expose] noncomputable def cntK (n : Nat) (p : Nat → Bool) : Nat :=
  foldN n (fun i s => nIf(p i, Nat.succ s, s)) 0

theorem zpts : bAnd(Nat.beq (zx 0) 0, bAnd(notB (Nat.beq (zx (nget S2308W 0)) (nget S2308W 0)),
    bAnd(Nat.blt (nget S2308W 0) 22880,
    bAnd(Nat.beq (cntK 22880 (fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i))) 280,
    bAnd(Nat.beq (cntK 22880 (fun i => Nat.beq (cf 3 i) i)) 38,
      Nat.beq (cntK 22880 (fun i => Nat.beq (cf 4 i) i)) 38))))) = true := by quickRfl

theorem rst : bAnd(allN 14 (fun j => allN 280 (fun i =>
      Nat.beq (fx j (ld i)) (ld (pg 9 (mask 9) (SuzLocR (Nat.add 8 j)) i)))),
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

theorem pts0 : penumSlK 280 9 (mask 9) (280 * 9) false S2308CE.G S2308CE.GI 5 S2308CE.cnt
    S2308CE.T S2308CE.PL S2308CE.POS S2308CE.SRT S2308CE.SRI 0 365 = true := by quickRfl
theorem pts1 : penumSlK 280 9 (mask 9) (280 * 9) false S2308CE.G S2308CE.GI 5 S2308CE.cnt
    S2308CE.T S2308CE.PL S2308CE.POS S2308CE.SRT S2308CE.SRI 365 365 = true := by quickRfl

@[expose] noncomputable def escP (k : Nat) : Bool :=
  strictB (S2308CE.T k) (fun t =>
    bIf(allN 5 (fun a => Nat.beq (pcomp 280 9 (mask 9) (S2308CE.G a) t)
        (pcomp 280 9 (mask 9) t (S2308CE.G a))),
      bIf(Nat.beq t (pidn 280 9), true, bIf(Nat.beq t (SuzCenC 3), true,
        Nat.beq t (pcomp 280 9 (mask 9) (SuzCenC 3) (SuzCenC 3)))), true))

theorem esc : allN 729 escP = true := by quickRfl

@[expose] noncomputable def cenP (x : Nat) : Bool :=
  bAnd(allN 9 (fun r => Nat.beq (cf r x) (o2 (itr (cf 3) (Nat.div r 3)) (itr zx (Nat.mod r 3)) x)),
  bAnd(Nat.beq (o2 (cf 1) (cf 1) x) (cf 2 x), bAnd(Nat.beq (o2 (cf 3) (cf 3) x) (cf 6 x),
  bAnd(Nat.beq (o2 (cf 4) (cf 4) x) (cf 8 x), bAnd(Nat.beq (o2 (cf 5) (cf 5) x) (cf 7 x),
  bAnd(Nat.beq (cf 3 x) (tx 1 x), bAnd(Nat.beq (o2 (cf 3) zx x) (o2 zx (cf 3) x),
  bAnd(allN 5 (fun a => bAnd(Nat.beq (o2 (cf 3) (tx a) x) (o2 (tx a) (cf 3) x),
    Nat.beq (o2 zx (tx a) x) (o2 (tx a) zx x))),
    Nat.beq (itr (cf 3) 3 x) x))))))))

theorem cq0 : qtr cenP 0 = true := by quickRfl
theorem cq1 : qtr cenP 1 = true := by quickRfl
theorem cq2 : qtr cenP 2 = true := by quickRfl
theorem cq3 : qtr cenP 3 = true := by quickRfl

theorem cdist : allN 9 (fun r => allN 9 (fun r' => bIf(Nat.blt r r',
    bAnd(Nat.blt (nget S2308W (Nat.add 1 (Nat.add (Nat.mul 9 r) r'))) 22880,
      notB (Nat.beq (cf r (nget S2308W (Nat.add 1 (Nat.add (Nat.mul 9 r) r'))))
        (cf r' (nget S2308W (Nat.add 1 (Nat.add (Nat.mul 9 r) r')))))), true))) = true := by
  quickRfl

@[expose] noncomputable def gP (x : Nat) : Bool :=
  bAnd(Nat.beq (gx x) (wpC fusW x), Nat.beq (o2 gx (o2 zx gxi) x) (cf 5 x))

theorem gq0 : qtr gP 0 = true := by quickRfl
theorem gq1 : qtr gP 1 = true := by quickRfl
theorem gq2 : qtr gP 2 = true := by quickRfl
theorem gq3 : qtr gP 3 = true := by quickRfl

theorem gperm : bAnd(rpermK 22880 15 (mask 15) S2308GX 0 S2308GXI 0, Nat.beq (gx 0) 95) = true := by
  quickRfl

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
