module

public import Certificates.Kernel.Th.DModel.Data
public import Certificates.Kernel.Th.AutD.Defs

public section

namespace CertificateChecks.KernelTh.DModel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KS.PEnum CertificateChecks.KernelTh CertificateChecks.KernelTh.AutD
open CFSG.Sporadic.Th.Recog
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def oT (r : Nat) : Nat → Nat :=
  [DPO0.T, DPO1.T, DPO2.T, DPO3.T, DPO4.T, DPO5.T, DPO6.T, DPO7.T, DPO8.T, DPO9.T, DPO10.T,
    DPO11.T].getD r DPO0.T

@[expose] noncomputable def oG (r : Nat) : Nat → Nat :=
  [DPO0.G, DPO1.G, DPO2.G, DPO3.G, DPO4.G, DPO5.G, DPO6.G, DPO7.G, DPO8.G, DPO9.G, DPO10.G,
    DPO11.G].getD r DPO0.G

@[expose] noncomputable def oGI (r : Nat) : Nat → Nat :=
  [DPO0.GI, DPO1.GI, DPO2.GI, DPO3.GI, DPO4.GI, DPO5.GI, DPO6.GI, DPO7.GI, DPO8.GI, DPO9.GI,
    DPO10.GI, DPO11.GI].getD r DPO0.GI

@[expose] noncomputable def oPL (r : Nat) : Nat → Nat :=
  [DPO0.PL, DPO1.PL, DPO2.PL, DPO3.PL, DPO4.PL, DPO5.PL, DPO6.PL, DPO7.PL, DPO8.PL, DPO9.PL,
    DPO10.PL, DPO11.PL].getD r DPO0.PL

@[expose] noncomputable def oPOS (r : Nat) : Nat → Nat :=
  [DPO0.POS, DPO1.POS, DPO2.POS, DPO3.POS, DPO4.POS, DPO5.POS, DPO6.POS, DPO7.POS, DPO8.POS,
    DPO9.POS, DPO10.POS, DPO11.POS].getD r DPO0.POS

@[expose] noncomputable def oSRT (r : Nat) : Nat → Nat :=
  [DPO0.SRT, DPO1.SRT, DPO2.SRT, DPO3.SRT, DPO4.SRT, DPO5.SRT, DPO6.SRT, DPO7.SRT, DPO8.SRT,
    DPO9.SRT, DPO10.SRT, DPO11.SRT].getD r DPO0.SRT

@[expose] noncomputable def oSRI (r : Nat) : Nat → Nat :=
  [DPO0.SRI, DPO1.SRI, DPO2.SRI, DPO3.SRI, DPO4.SRI, DPO5.SRI, DPO6.SRI, DPO7.SRI, DPO8.SRI,
    DPO9.SRI, DPO10.SRI, DPO11.SRI].getD r DPO0.SRI

@[expose] noncomputable def oc (r : Nat) : Nat :=
  [DPO0.cnt, DPO1.cnt, DPO2.cnt, DPO3.cnt, DPO4.cnt, DPO5.cnt, DPO6.cnt, DPO7.cnt, DPO8.cnt,
    DPO9.cnt, DPO10.cnt, DPO11.cnt].getD r 0

@[expose] noncomputable def ok (r : Nat) : Nat :=
  [DPO0.k, DPO1.k, DPO2.k, DPO3.k, DPO4.k, DPO5.k, DPO6.k, DPO7.k, DPO8.k, DPO9.k, DPO10.k,
    DPO11.k].getD r 0

@[expose] noncomputable def oX (r : Nat) : Nat := wK L LI (primeReps.getD r [])

@[expose] noncomputable def kerK (X : Nat) (Ls : List (List (Fin 6 × Bool) × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 51 6)
    (fun ck _ acc => pc (pc (pc (wK L LI ck.1)
      (Bool.rec (motive := fun _ => Nat) X (pc X X) (Nat.beq ck.2 2)))
      (wK L LI (FreeGroup.invRev ck.1))) acc) Ls

@[expose] noncomputable def tgtK (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (LI 5) (L 5) (Nat.beq i 1)) (L 0) (Nat.beq i 0)

@[expose] noncomputable def inR (r x : Nat) : Bool :=
  notB (allN (oc r) fun q => notB (Nat.beq (oT r q) x))

@[expose] noncomputable def inO (x : Nat) : Bool := notB (allN 12 fun r => notB (inR r x))

@[expose] noncomputable def ptD (i : Nat) : Bool :=
  strictB (ADE.T i) fun t => strictB (pc t t) fun t2 =>
    orB (Nat.beq t (pidn 51 6)) (orB (andB (notB (Nat.beq t2 (pidn 51 6)))
      (notB (Nat.beq (pc t t2) (pidn 51 6)))) (inO t))

@[expose] noncomputable def sqD (i : Nat) : Bool := Nat.beq (pc (ADE.T i) (ADE.T i)) (pidn 51 6)

@[expose] noncomputable def cSl (s : Nat) : Bool :=
  allN 384 fun d => strictB (Nat.add (Nat.mul 384 s) d) ptD

end CertificateChecks.KernelTh.DModel

end
