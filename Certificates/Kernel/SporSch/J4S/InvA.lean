
module

public import Certificates.Kernel.SporSch.J4S.InvW
public import Certificates.Kernel.SporSch.J4S.InvC
public import CFSG.Certificates.Kernel.SporSch.J4SPowBSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4InvA

open CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta
open CertificateChecks.KernelSporSch.J4InvC

@[expose] noncomputable def KL : List Nat :=
  [getN one J4K0 0, getN one J4K1 0, getN one J4K2 0, getN one J4K3 0,
    getN one J4K0 170, getN one J4K1 59, getN one J4K2 3, getN one J4K3 4]

@[expose] noncomputable def p0 (e : Nat) : Nat := CFSG.KS.SporSch.C11.ent 10 (J4D.T e) 0
@[expose] noncomputable def p1 (e : Nat) : Nat := CFSG.KS.SporSch.C11.ent 10 (J4D.T e) 1

@[expose] noncomputable def uF (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => one)
    (fun _ ih e => nIf(bAnd(Nat.blt 0 e, Nat.blt (p0 e) e),
      CFSG.KC.Loop.strictN (ih (p0 e)) fun u => mulJ c rm u (getN one KL (p1 e)), one)) f

@[expose] noncomputable def uS (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => one)
    (fun _ ih e => nIf(bAnd(Nat.blt 0 e, Nat.blt (p0 e) e),
      CFSG.KC.Loop.strictN (ih (p0 e)) fun u => mulJ c rm (getN one KL (Nat.add 4 (p1 e))) u,
      one)) f

@[expose] noncomputable def getW (L : List (List Int)) (i : Nat) : List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Int) x (fun m _ => ih m) i) L i

@[expose] noncomputable def ambB (wf ws ef1 ef2 uf us sf ss s : Nat) : Bool :=
  strictB (mulJ c rm ef1 uf) fun a1 => strictB (mulJ c rm us ef2) fun a2 =>
  strictB (powBK c rm one 45 (mulJ c rm a1 (mulJ c rm (mulJ c rm wf sf) ws)) hExp) fun p1 =>
  strictB (powBK c rm one 45 (mulJ c rm (mulJ c rm wf (mulJ c rm ss ws)) a2) hExp) fun p2 =>
  bAnd(Nat.beq (mulJ c rm (mulJ c rm (mulJ c rm ws p1) a1) (mulJ c rm p2 wf)) sf,
    bIf(Nat.beq s 1, true, Nat.beq s 14))

@[expose] noncomputable def rootK (i : Nat) : Bool :=
  strictB (AH 0 i) fun n => strictB (AH 1 i) fun e =>
  strictB (AH 2 i) fun s =>
  strictB (wFK c rm one A A B Bi (getW J4AW.ws i) one) fun wf =>
  strictB (wSK c rm one A A B Bi (getW J4AW.ws i) one) fun ws =>
  strictB (prodFK c rm one (ef n)) fun ef1 =>
  strictB (prodSK c rm one (es n)) fun ef2 =>
  strictB (uF 1024 e) fun uf => strictB (uS 1024 e) fun us =>
  strictB (prodFK c rm one (ef s)) fun sf =>
  strictB (prodSK c rm one (es s)) fun ss =>
  ambB wf ws ef1 ef2 uf us sf ss s

theorem lettersA : ∀ w ∈ J4AW.ws, ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by decide +kernel

end CertificateChecks.KernelSporSch.J4InvA

#kss_slices CertificateChecks.KernelSporSch.J4IA CertificateChecks.KernelSporSch.J4InvA.rootK 1 77

end
