module

public import Certificates.Kernel.Sporadic.Fi22.Cent17336D
public import Certificates.Kernel.Sporadic.Fi22.Five8124K
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
public import Certificates.Data.Kernel.Fi22Cent.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Cent17336

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fi22Cent
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fv8124 (ev idP pwK isP)

@[expose] noncomputable def D : Nat := Fi22C17336T.F 0
@[expose] noncomputable def X : Nat := Fi22C17336T.F 1
@[expose] noncomputable def A0 : Nat := Fi22CGT.F 0
@[expose] noncomputable def A1 : Nat := Fi22CGT.F 1

@[expose] noncomputable def gp (a0 a1 a1i j : Nat) : Nat := nIf(Nat.beq j 0, a0, nIf(Nat.beq j 1, a1, a1i))

@[expose] noncomputable def gi (a0i a1 a1i j : Nat) : Nat :=
  nIf(Nat.beq j 0, a0i, nIf(Nat.beq j 1, a1i, a1))

@[expose] noncomputable def at12 (r p : Nat) : Nat := pg 12 (mask 12) r p

@[expose] noncomputable def chkDX (d x : Nat) : Bool :=
  isP d && isP x && Fi22X.siftP d && Fi22X.siftP x && Nat.beq (Fi22X.c d d) idP &&
    Nat.beq (pwK x 3) idP && !(Nat.beq x idP) &&
    Nat.beq (Fi22X.c (Fi22X.c d x) (Fi22X.c d x)) idP &&
    Nat.beq (ev x 0) 1 && !(Nat.beq (ev x 1) 0) && !(Nat.beq (ev x 1) 1) &&
    Nat.beq (cntN (ev x) 3510) 126

@[expose] noncomputable def chkS (d x s : Nat) : Bool :=
  isP s && (!(Nat.beq (ev s 0) 0) || Nat.beq (Fi22X.c s d) (Fi22X.c d s)) &&
    (!(Nat.beq (ev s 0) 0 && Nat.beq (ev s 1) 1) || Nat.beq (Fi22X.c s x) (Fi22X.c x s))

@[expose] noncomputable def chkT (a0 a1 a1i P0 P1 P2 : Nat) : Bool :=
  isP a0 && isP a1 &&
    allN 3510 (treeRow (fun j y => ev (gp a0 a1 a1i j) y) (at12 P0) (at12 P1) (at12 P2))

@[expose] noncomputable def dpF (a0 a1 a0i a1i d P0 P1 p y : Nat) : Nat :=
  tApp (fun j z => ev (gp a0 a1 a1i j) z) (at12 P0) (at12 P1) 64 p
    (ev d (tInv (fun j z => ev (gi a0i a1 a1i j) z) (at12 P0) (at12 P1) 64 p y))

@[expose] noncomputable def chkI (a0 a1 a0i a1i d x P0 P1 P3 : Nat) : Bool :=
  allN 3510 (invRow (dpF a0 a1 a0i a1i d P0 P1) (ev x) (at12 P3))

theorem okDX : strictB D (fun d => strictB X fun x => chkDX d x) = true := by quickRfl

theorem okS : strictB D (fun d => strictB X fun x =>
    allN 19 fun j => strictB (Fi22ChT.F j) fun s => chkS d x s) = true := by quickRfl

theorem okT : strictB A0 (fun a0 => strictB A1 fun a1 => strictB (Fi22X.inv a1) fun a1i =>
    strictB (Fi22CentR.R 0) fun P0 => strictB (Fi22CentR.R 1) fun P1 =>
      strictB (Fi22CentR.R 2) fun P2 => chkT a0 a1 a1i P0 P1 P2) = true := by quickRfl

theorem okI : strictB A0 (fun a0 => strictB A1 fun a1 => strictB (Fi22X.inv a0) fun a0i =>
    strictB (Fi22X.inv a1) fun a1i => strictB D fun d => strictB X fun x =>
      strictB (Fi22CentR.R 0) fun P0 => strictB (Fi22CentR.R 1) fun P1 =>
        strictB (Fi22CentR.R 3) fun P3 => chkI a0 a1 a0i a1i d x P0 P1 P3) = true := by quickRfl

end CertificateChecks.KernelSpor.Cent17336

end
