module

public import Certificates.Kernel.Sporadic.Fi22.L17337R
public import Certificates.Kernel.Sporadic.Fi22.Five8124K
public import Certificates.Data.Kernel.Fi22Cent.Words
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.L17337

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fi22Cent
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fv8124 (ev isP)

@[expose] def LB : Array Nat := #[19, 2, 3, 0, 1, 6, 4]

@[expose] noncomputable def A : Nat := Fi22L17.S 0
@[expose] noncomputable def B : Nat := Fi22L17.S 1
@[expose] noncomputable def X : Nat := Fi22LT.F 1

@[expose] noncomputable def letF (a b ai bi : Nat) (l : Fin 2 × Bool) (y : Nat) : Nat :=
  ev (cond l.2 (nIf(Nat.beq l.1.val 0, a, b)) (nIf(Nat.beq l.1.val 0, ai, bi))) y

@[expose] noncomputable def chkR (a b ai bi : Nat) : Bool :=
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.relsU43.all fun w =>
    [0, 1, 2, 3, 6, 4].all fun p => Nat.beq (wAt (letF a b ai bi) w p) p

@[expose] noncomputable def chkA (a b x : Nat) : Bool :=
  isP x && Nat.beq (ev a 0) 0 && Nat.beq (ev a 1) 1 && Nat.beq (ev b 0) 0 &&
    Nat.beq (ev b 1) 1 && Nat.beq (Fi22X.c a x) (Fi22X.c x a) &&
    Nat.beq (Fi22X.c b x) (Fi22X.c x b)

theorem okB : (allN 8 fun j => Nat.beq (Fi22L17.S j) (Fi22LT.F (Nat.add 2 j))) &&
    (allN 7 fun t => Nat.beq LB[t]! (pg 12 (mask 12) Fi22L17.BP t)) = true := by quickRfl

theorem okP : (allN 8 fun j => strictB (Fi22L17.S j) fun s => isP s && Fi22X.siftP s) = true := by
  quickRfl

theorem okA : strictB A (fun a => strictB B fun b => strictB X fun x => chkA a b x) = true := by
  quickRfl

theorem okR : strictB A (fun a => strictB B fun b => strictB (Fi22X.inv A) fun ai =>
    strictB (Fi22X.inv B) fun bi => chkR a b ai bi) = true := by quickRfl

theorem orbits : (List.range 7).map (fun i => rcnt (Fi22L17.LR i)) = [126, 432, 60, 1, 1, 1, 1] := by
  decide +kernel

end CertificateChecks.KernelSpor.L17337

end
