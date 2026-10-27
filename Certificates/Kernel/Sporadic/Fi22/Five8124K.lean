module

public import Certificates.Kernel.Sporadic.Fi22.Five8124D
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.F1OuterT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fv8124

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CertificateChecks.KernelSpor

@[expose] noncomputable def ev (P x : Nat) : Nat := pg 12 (mask 12) P x

@[expose] noncomputable def idP : Nat := pidn 3510 12

@[expose] noncomputable def pwK (p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idP (fun _ acc => Fi22X.c p acc) k

@[expose] noncomputable def isP (p : Nat) : Bool :=
  Fi22X.cn p && permOK 3510 12 (mask 12) (3510 * 12) p (Fi22X.inv p)

@[expose] noncomputable def lineK (Q1 Q2 j : Nat) : Nat :=
  cond (Nat.beq j 1) Q2 (Fi22X.c Q1 (pwK Q2 (j - 1)))

@[expose] noncomputable def memE (x : Nat) : Bool :=
  !(allN 60 fun i => !(Nat.beq (Fv8124E.T i) x))

@[expose] noncomputable def difAt (f g : Nat → Nat) : Bool :=
  CFSG.RankThree.Native.fi22FiveKeyPts.any fun p => !(Nat.beq (f p) (g p))

@[expose] noncomputable def chkQ (Q1 Q2 : Nat) : Bool :=
  isP Q1 && isP Q2 && Nat.beq (Fi22X.c Q1 Q2) (Fi22X.c Q2 Q1) &&
    Nat.beq (pwK Q1 5) idP && Nat.beq (pwK Q2 5) idP && !(Nat.beq Q1 idP) &&
    allN 5 fun e => !(Nat.beq Q2 (pwK Q1 e))

@[expose] noncomputable def chkW (W U : Nat) : Bool :=
  isP W && Nat.beq (Fi22X.c W W) idP && !(Nat.beq W idP) && !(Fi22X.siftP W) &&
    Fi22X.cn (Fi22X.c U W) && Fi22X.siftP (Fi22X.c U W)

@[expose] noncomputable def chkH (Q1 Q2 W H j : Nat) : Bool :=
  isP H && Fi22X.siftP H && Nat.beq (Fi22X.c H (lineK Q1 Q2 j)) (Fi22X.c Q1 H) &&
    Nat.beq (Fi22X.c H W) (Fi22X.c W H)

@[expose] noncomputable def chk0 (Q1 Q2 W A Q2i Ai D1 : Nat) : Bool :=
  isP A && Fi22X.siftP Q1 && Fi22X.siftP Q2 && Fi22X.siftP A &&
    Nat.beq (Fi22X.c A Q1) (Fi22X.c Q1 A) && Nat.beq (Fi22X.c W Q1) (Fi22X.c Q1 W) &&
    Nat.beq (Fi22X.c A W) (Fi22X.c W A) && Nat.beq (Fi22X.c Q2 W) (Fi22X.c W Q2) &&
    strictB (Fi22X.c A (Fi22X.c Q2i Q2i)) (fun G =>
      strictB (Fi22X.c Q2i (Fi22X.c Q2i (Fi22X.c A Q2i))) fun H =>
        Nat.beq (Fi22X.c G H) (Fi22X.c Q2 (Fi22X.c H G))) &&
    Nat.beq D1 (Fi22X.c (Fi22X.c A Q2) (Fi22X.c Ai Q2i)) &&
    Nat.beq Fv8124E.ng 2 && Nat.beq Fv8124E.N 60 &&
    Nat.beq (Fv8124E.G 0) D1 && Nat.beq (Fv8124E.G 1) Q2 &&
    memE (Fi22X.c A (Fi22X.c D1 Ai)) && memE (Fi22X.c A (Fi22X.c Q2 Ai)) &&
    memE (Fi22X.c Q2 (Fi22X.c D1 Q2i)) &&
    !(Nat.beq (Fi22X.c D1 Q2) (Fi22X.c Q2 D1))

@[expose] noncomputable def orbRow (O : List Nat) (t : Nat) : Bool :=
  O.all (fun o => O.contains (ev t o)) && (!(O.all fun o => Nat.beq (ev t o) o) || Nat.beq t idP)

@[expose] noncomputable def chkD (Q1i Q2 A D1 : Nat) (O : List Nat) : Bool :=
  (allN 60 fun i => orbRow O (Fv8124E.T i)) &&
    (allN 5 fun e => strictB (Fi22X.c A (pwK Q1i e)) fun y => !(memE y)) &&
    allN 60 fun i => strictB (Fv8124E.T i) fun t =>
      difAt (fun p => ev A (ev t (ev D1 p))) (fun p => ev D1 (ev A (ev t p))) ||
        difAt (fun p => ev A (ev t (ev Q2 p))) (fun p => ev Q2 (ev A (ev t p)))

@[expose] noncomputable def Q1 : Nat := Fv8124T.F 0
@[expose] noncomputable def Q2 : Nat := Fv8124T.F 1
@[expose] noncomputable def W : Nat := Fv8124T.F 2
@[expose] noncomputable def H (j : Nat) : Nat := Fv8124T.F (j + 2)
@[expose] noncomputable def A : Nat := Fi22OutT.L 1

theorem okQ : strictB Q1 (fun q1 => strictB Q2 fun q2 => chkQ q1 q2) = true := by quickRfl

theorem okW : strictB W (fun w => chkW w Fi22X.GO) = true := by quickRfl

theorem okH : strictB Q1 (fun q1 => strictB Q2 fun q2 => strictB W fun w =>
    allN 5 fun j => strictB (H (j + 1)) fun h => chkH q1 q2 w h (j + 1)) = true := by quickRfl

theorem ok0 : strictB Q1 (fun q1 => strictB Q2 fun q2 => strictB W fun w => strictB A fun a =>
    strictB (Fi22X.inv Q2) fun q2i => strictB (Fi22X.inv A) fun ai =>
      strictB (Fi22X.c (Fi22X.c a q2) (Fi22X.c ai q2i)) fun d1 =>
        chk0 q1 q2 w a q2i ai d1) = true := by quickRfl

theorem okD : strictB (Fi22X.inv Q1) (fun q1i => strictB Q2 fun q2 => strictB A fun a =>
    strictB (Fv8124E.G 0) fun d1 =>
      chkD q1i q2 a d1 (CFSG.RankThree.Native.fi22FiveOrbits[0]!)) = true := by quickRfl

theorem negH : strictB Q1 (fun q1 => strictB Q2 fun q2 => strictB W fun w =>
    !(chkH q1 q2 w (H 2) 1) && !(chkH q1 q2 w q1 1)) = true := by quickRfl

theorem negD : strictB (Fi22X.inv Q1) (fun q1i => strictB Q2 fun q2 =>
    strictB (Fv8124E.G 0) fun d1 =>
    !(allN 60 fun i => orbRow (CFSG.RankThree.Native.fi22FiveOrbits[1]!) (Fv8124E.T i)) &&
      !(chkD q1i q2 idP d1 (CFSG.RankThree.Native.fi22FiveOrbits[0]!))) = true := by quickRfl

end CertificateChecks.KernelSpor.Fv8124

end
