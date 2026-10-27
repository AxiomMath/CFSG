module

public import Certificates.Kernel.Sporadic.Fi22.Pump36908D
public import Certificates.Kernel.Sporadic.Fi22.Five8124K
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Fi22Reps.Each
public import Certificates.Data.Kernel.Fi22Pump.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Pump36908

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fi22Pump CFSG.KC.PtOrb
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fv8124 (ev idP pwK isP)
open CertificateChecks.KernelFi22Reps (LT xT)
open CFSG.KC.Fi22S0 (ent)

@[expose] noncomputable def S : Nat := Fi22PumpT.F 0

@[expose] noncomputable def Y (j : Nat) : Nat := Fi22PumpT.F (Nat.succ j)

@[expose] noncomputable def chkS (s A B : Nat) : Bool :=
  isP s && sigC (ev s) (ent A) (ev (Fi22CGT.F 0)) && sigC (ev s) (ent B) (ev (Fi22CGT.F 1))

@[expose] noncomputable def chkY (s si t y : Nat) : Bool :=
  isP y && Fi22X.siftP y && Nat.beq (pwK y 5) idP && !(Nat.beq y idP) &&
    commC (ev y) (fun x => ev s (ent t (ev si x)))

@[expose] noncomputable def gY (y0 y1 j : Nat) : Nat → Nat := ev (nIf(Nat.beq j 0, y0, y1))

theorem okS : strictB S (fun s => strictB (LT 0) fun A => strictB (LT 1) fun B => chkS s A B) =
    true := by quickRfl

theorem okC0 : strictB (xT 0) (fun t => Nat.beq (cntF (ent t)) 0) = true := by quickRfl

theorem okC1 : strictB (xT 1) (fun t => Nat.beq (cntF (ent t)) 27) = true := by quickRfl

theorem okC2 : strictB (xT 2) (fun t => Nat.beq (cntF (ent t)) 36) = true := by quickRfl

theorem okC3 : strictB (xT 3) (fun t => Nat.beq (cntF (ent t)) 126) = true := by quickRfl

theorem okY : strictB S (fun s => strictB (Fi22X.inv s) fun si => strictB (xT 3) fun t =>
    allN 2 fun j => strictB (Y j) fun y => chkY s si t y) = true := by quickRfl

theorem okO : strictB (Y 0) (fun y0 => strictB (Y 1) fun y1 => orbC (gY y0 y1) 2 16 1 1260) =
    true := by quickRfl

end CertificateChecks.KernelSpor.Pump36908

end
