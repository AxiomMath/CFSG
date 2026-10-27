module

public import Certificates.Data.Kernel.U43CentPlus.Defs
public import Certificates.Kernel.U43CentPlus.Data
public import Certificates.Kernel.U43Mod.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43CentPlus

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43CentPlus CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelU43Mod

@[expose] noncomputable def GE (i q : Nat) : Nat := pg 10 (mask 10) (ET i) q

@[expose] noncomputable def GQ (j q : Nat) : Nat := pg 10 (mask 10) (QT j) q

@[expose] noncomputable def GT (k q : Nat) : Nat := pg 10 (mask 10) (TT k) q

@[expose] noncomputable def GY (r q : Nat) : Nat := pg 10 (mask 10) (YT r) q

@[expose] noncomputable def GC (c q : Nat) : Nat :=
  GQ (Nat.mod c (nat_lit 32)) (GT (Nat.div c (nat_lit 32)) q)

@[expose] noncomputable def G0P (q : Nat) : Nat := GQ (G0 0) (GT (G0 1) q)

@[expose] noncomputable def commA (f : Nat → Nat) : Bool :=
  baseEq bs (fun q => f (GA 0 q)) (fun q => GA 0 (f q))

@[expose] noncomputable def rootA (f : Nat → Nat) : Bool :=
  baseEq bs (fun q => f (f q)) (GA 0)

@[expose] def ix32 : List Nat := List.range 32

@[expose] noncomputable def GP (i x : Nat) : Nat := fld(PT i, Nat.mul (nat_lit 5) x, nat_lit 31)

theorem kE : allN 4 (fun i => bAnd(permOK 820 10 (mask 10) (820 * 10) (ET i) (ETI i),
    bAnd(inPU (ET i), baseEq bs (GE i) (GM i)))) = true := by
  quickRfl

theorem kQ : allN 32 (fun j => bAnd(permOK 820 10 (mask 10) (820 * 10) (QT j) (QTI j),
    bAnd(inPU (QT j), commA (GQ j)))) = true := by
  quickRfl

theorem kT : (Nat.beq (TT 0) (pidn 820 10) && allN 4 (fun k =>
    bAnd(permOK 820 10 (mask 10) (820 * 10) (TT k) (TTI k), bAnd(inPU (TT k), commA (GT k))))) =
    true := by
  quickRfl

theorem kQinc : incK 32 (fun j => bKey (GQ j)) = true := by quickRfl

theorem kMT : allN 32 (fun i => allN 32 (fun j => strictB fld(MT i, Nat.mul 5 j, 31) (fun x =>
    bAnd(Nat.blt x 32, baseEq bs (fun q => GQ i (GQ j q)) (GQ x))))) = true := by
  quickRfl

theorem kPI : allN 4 (fun i => allN 32 (fun j => strictB (GP i j) (fun x =>
    bAnd(Nat.blt x 32, baseEq bs (fun q => GE i (GQ j q)) (fun q => GQ x (GE i q)))))) = true := by
  quickRfl

theorem kIA : (Nat.blt (IA 0) 32 && baseEq bs (GQ (IA 0)) (GA 0)) = true := by quickRfl

theorem kTM : allN 3 (fun i => allN 3 (fun j => strictB (TM (Nat.add (Nat.mul 3 i) j)) (fun v =>
    bAnd(Nat.blt v 128, baseEq bs (fun q => GT (Nat.succ i) (GT (Nat.succ j) q)) (GC v))))) =
    true := by
  quickRfl

theorem kL : (allN 128 (fun c => Nat.blt (LT c) 128) && incK 128 (fun c => bKey (GC (LT c)))) =
    true := by
  quickRfl

theorem kY : (Nat.blt (G0 0) 32 && Nat.blt (G0 1) 4 &&
    cTree 820 10 (mask 10) YT YR 72 4 ET ETI (QT (G0 0)) (TT (G0 1)) &&
    incK 72 (fun r => bKey (GY r))) = true := by
  quickRfl

theorem kRoot : allN 3 (fun k => allN 32 (fun j =>
    strictB (Nat.add (Nat.mul 32 (Nat.succ k)) j) (fun c => bIf(rootA (GC c),
      strictB (RI (Nat.add (Nat.mul 32 k) j)) (fun r => bAnd(Nat.blt r 72, baseEq bs (GC c) (GY r))),
      true)))) = true := by
  quickRfl

theorem kD : (allN 16 (fun i => Nat.blt (DT i) 128) && incK 16 (fun i => bKey (GC (DT i))) &&
    allN 16 (fun i => baseEq bs (fun q => GC (DT i) (G0P q)) (fun q => G0P (GC (DT i) q))) &&
    Nat.beq (cntN 16 (fun i => rootA (GC (DT i)))) 4) = true := by
  quickRfl

theorem kKP : kTree KP 5 (mask 5) 10 (mask 10) ix32 576 4 GP = true := by quickRfl

end CertificateChecks.KernelU43CentPlus

end
