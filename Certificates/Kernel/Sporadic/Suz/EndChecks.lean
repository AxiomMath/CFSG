module

public import Certificates.Kernel.Sporadic.Suz.EndData
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import CFSG.Certificates.Kernel.SporSch.AnyN
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.SporSch.MathieuOC
public import Certificates.Data.Kernel.Spor.Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzEnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

@[expose] noncomputable def fv (P i : Nat) : Nat := pg 11 (mask 11) P i

@[expose] noncomputable def ne (a b : Nat) : Bool := bIf(Nat.beq a b, false, true)

@[expose] noncomputable def bor (a b : Bool) : Bool := bIf(a, true, b)

@[expose] noncomputable def E0 : Nat := SuzEndE.F 0

@[expose] noncomputable def E1 : Nat := SuzEndE.F 1

@[expose] noncomputable def T0 : Nat := SuzTP 0

@[expose] noncomputable def fc (P : Nat) : Nat := fixCntK 1782 11 (mask 11) P

@[expose] noncomputable def eK : Bool :=
  allN 1782 fun p => bAnd(Nat.beq (fv E0 (fv E0 p)) p, bAnd(Nat.beq (fv E1 (fv E1 p)) p,
    Nat.beq (fv E0 (fv E1 p)) (fv E1 (fv E0 p))))

@[expose] noncomputable def fK : Bool :=
  bAnd(Nat.beq (fc E0) 42, bAnd(Nat.beq (fc E1) 42,
    Nat.beq (fc (pcomp 1782 11 (mask 11) E0 E1)) 42))

@[expose] noncomputable def pK : Bool :=
  bAnd(permOK 1782 11 (mask 11) (1782 * 11) E0 (EI 0),
    bAnd(permOK 1782 11 (mask 11) (1782 * 11) E1 (EI 1),
    bAnd(permOK 1782 11 (mask 11) (1782 * 11) B BI,
    bAnd(permOK 1782 11 (mask 11) (1782 * 11) T0 T0,
    bAnd(allN 2 (fun i => permOK 1782 11 (mask 11) (1782 * 11) (SG i) (SGI i)),
    bAnd(allN 8 (fun i => permOK 1782 11 (mask 11) (1782 * 11) (X i) (XI i)),
      allN 6 (fun i => permOK 1782 11 (mask 11) (1782 * 11) (Y i) (YI i))))))))

@[expose] noncomputable def mK : Bool :=
  bAnd(Suz2306.sift E0, bAnd(Suz2306.sift E1, bAnd(Suz2306.sift B,
    bAnd(Suz2306.sift (SG 0), Suz2306.sift (SG 1)))))

@[expose] noncomputable def siftX (i : Nat) : Bool := Suz2306.sift (X i)

@[expose] noncomputable def siftL (j : Nat) : Bool := Suz2306.sift (SuzEL.S j)

@[expose] noncomputable def cB (E E' p : Nat) : Bool :=
  Nat.beq (fv E (fv BI (fv E' (fv B p)))) (fv BI (fv E' (fv B (fv E p))))

@[expose] noncomputable def bcK : Bool :=
  allN 1782 fun p => bAnd(cB E0 E0 p, bAnd(cB E0 E1 p, bAnd(cB E1 E0 p, cB E1 E1 p)))

@[expose] noncomputable def cC (p : Nat) : Nat := fv BI (fv E0 (fv B p))

@[expose] noncomputable def bnK : Bool :=
  bAnd(anyN 1782 (fun p => ne (cC p) p), bAnd(anyN 1782 (fun p => ne (cC p) (fv E0 p)),
    bAnd(anyN 1782 (fun p => ne (cC p) (fv E1 p)),
      anyN 1782 (fun p => ne (cC p) (fv E0 (fv E1 p))))))

@[expose] noncomputable def xcK : Bool :=
  allN 8 fun i => allN 1782 fun p => bAnd(Nat.beq (fv (X i) (fv E0 p)) (fv E0 (fv (X i) p)),
    Nat.beq (fv (X i) (fv E1 p)) (fv E1 (fv (X i) p)))

@[expose] noncomputable def cm (P Q PI QI p : Nat) : Nat := fv P (fv Q (fv PI (fv QI p)))

@[expose] noncomputable def trK : Bool :=
  allN 1782 fun p => bAnd(allN 4 (fun j => Nat.beq (fv (Y j) p)
      (cm (X (Nat.mul 2 j)) (X (Nat.add (Nat.mul 2 j) 1)) (XI (Nat.mul 2 j))
        (XI (Nat.add (Nat.mul 2 j) 1)) p)),
    bAnd(Nat.beq (fv (Y 4) p) (cm (Y 0) (Y 1) (YI 0) (YI 1) p),
      bAnd(Nat.beq (fv (Y 5) p) (cm (Y 2) (Y 3) (YI 2) (YI 3) p),
        Nat.beq (cm (Y 4) (Y 5) (YI 4) (YI 5) p) (fv E0 (cC p)))))

@[expose] noncomputable def lcK : Bool :=
  allN 4 fun j => allN 1782 fun p =>
    bAnd(Nat.beq (fv (SuzEL.S j) (fv E0 p)) (fv E0 (fv (SuzEL.S j) p)),
      Nat.beq (fv (SuzEL.S j) (fv E1 p)) (fv E1 (fv (SuzEL.S j) p)))

@[expose] noncomputable def nthW (ws : List (List Nat)) (j : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) ws j

@[expose] noncomputable def wpt (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun i _ ih p => ih (fv (nIf(Nat.beq i 0, SuzEL.S 0, SuzEL.S 1)) p)) w p

@[expose] noncomputable def swK (j : Nat) : Bool :=
  allN 1782 fun p => Nat.beq (fv (SuzES.S j) p) (wpt (nthW suzEndSWords j) p)

@[expose] noncomputable def elemOK (j : Nat) : Bool :=
  strictB (elemK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzES.LR SuzES.TR 1 j) fun Z =>
    bor (anyN 1782 fun p => ne (fv Z (fv Z p)) p)
      (bor (allN 1782 fun p => Nat.beq (fv Z p) p) (ne (fc Z) 42))

@[expose] noncomputable def sgK : Bool :=
  bAnd(allN 1782 (fun p => Nat.beq (fv (SG 0) (fv E0 p)) (fv E0 (fv (SG 0) p))),
    bAnd(anyN 1782 (fun p => ne (fv (SG 0) (fv E1 p)) (fv E1 (fv (SG 0) p))),
      allN 1782 (fun p => Nat.beq (fv (SG 1) (fv E0 (fv (SGI 1) p))) (fv T0 p))))

theorem eOK : eK = true := by quickRfl
theorem fOK : fK = true := by quickRfl
theorem pOK : pK = true := by quickRfl
theorem mOK : mK = true := by quickRfl
theorem bcOK : bcK = true := by quickRfl
theorem bnOK : bnK = true := by quickRfl
theorem xcOK : xcK = true := by quickRfl
theorem trOK : trK = true := by quickRfl
theorem lcOK : lcK = true := by quickRfl
theorem sgOK : sgK = true := by quickRfl
theorem cntL : bAnd(Nat.beq (rcnt (SuzEL.LR 0)) 1260, Nat.beq (rcnt (SuzEL.LR 1)) 16) = true := by
  quickRfl
theorem cntS : Nat.beq (rcnt (SuzES.LR 0)) 64 = true := by quickRfl

meta def swapM : Array Nat := ((Array.range 1782).set! 0 1).set! 1 0

end CertificateChecks.KernelSpor.SuzEnd

#kss_each CertificateChecks.KernelSpor.SuzEndMX CertificateChecks.KernelSpor.SuzEnd.siftX 8
#kss_each CertificateChecks.KernelSpor.SuzEndML CertificateChecks.KernelSpor.SuzEnd.siftL 4
#kss_each CertificateChecks.KernelSpor.SuzEndSW CertificateChecks.KernelSpor.SuzEnd.swK 4
#ks_perm CertificateChecks.KernelSpor.SuzEnd.SWP 11 CertificateChecks.KernelSpor.SuzEnd.swapM

namespace CertificateChecks.KernelSpor.SuzEnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

theorem negE0 : bIf(bor (anyN 1782 fun p => ne (fv E0 (fv E0 p)) p)
    (bor (allN 1782 fun p => Nat.beq (fv E0 p) p) (ne (fc E0) 42)), false, true) = true := by
  quickRfl

theorem negSift : bIf(Suz2306.sift SWP, false, true) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzEnd

end
