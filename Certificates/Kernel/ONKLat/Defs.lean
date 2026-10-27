module

public import Certificates.Kernel.ONKLat.Data
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporONCheckInputs
public import Certificates.Kernel.Sporadic.OddCore.ON2129

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONKL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.ONSchreier
open CertificateChecks.KernelSpor

@[expose] noncomputable def commF (n w y t : Nat) : Bool :=
  bIf(Nat.beq (pg w (mask w) t (pg w (mask w) y 0)) (pg w (mask w) y (pg w (mask w) t 0)),
    Nat.beq (pcomp n w (mask w) t y) (pcomp n w (mask w) y t), false)

@[expose] noncomputable def qC (y i : Nat) : Bool := strictB (ON5M.T i) fun t => commF 120 7 y t

@[expose] noncomputable def slIn (P : List Nat) (s : Nat) : List Nat :=
  P.filter fun i => decide (2016 * s ≤ i) && decide (i < 2016 * s + 2016)

@[expose] noncomputable def cS (y : Nat) (P : List Nat) (s : Nat) : Bool :=
  selFrom (qC y) 2016 (Nat.mul s 2016) (slIn P s)

@[expose] noncomputable def y5 : Nat := List.getD yP 0 0

@[expose] noncomputable def y7 : Nat := List.getD yP 1 0

@[expose] noncomputable def c5S (s : Nat) : Bool := cS y5 c5 s

@[expose] noncomputable def c7S (s : Nat) : Bool := cS y7 c7 s

@[expose] noncomputable def powP (n w y : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ ih => pcomp n w (mask w) y ih) k

@[expose] noncomputable def yOK (r y p : Nat) : Bool :=
  bAnd(Nat.beq (ON5M.T p) y, bAnd(Nat.beq (powP 120 7 y r) (pidn 120 7),
    bIf(Nat.beq y (pidn 120 7), false, true)))

@[expose] noncomputable def m6 (p q : Nat) : Nat := pcomp 32 6 (mask 6) p q

@[expose] noncomputable def i32 : Nat := pidn 32 6

@[expose] noncomputable def cm6 (a b : Nat) : Bool := Nat.beq (m6 a b) (m6 b a)

@[expose] noncomputable def conjS (j t : Nat) : Nat := m6 (m6 (T32E.G j) t) (T32E.GI j)

@[expose] noncomputable def inD (D : List Nat) (t : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun d _ ih => bIf(Nat.beq t d, true, ih)) D

@[expose] noncomputable def invK (D : List Nat) (i : Nat) : Bool :=
  strictB (T32E.T i) fun t => bIf(Nat.beq (m6 t t) i32, bIf(Nat.beq t i32, true,
    bIf(allN 6 (fun j => cm6 t (conjS j t)), inD D t, true)), true)

@[expose] noncomputable def wW (t : Nat) : Nat :=
  nIf(Nat.blt t 36, m6 (m6 (m6 (T32E.G (t / 6)) (T32E.G (t % 6))) (T32E.GI (t / 6)))
      (T32E.GI (t % 6)),
    m6 (T32E.G (t - 36)) (m6 (T32E.G (t - 36)) (m6 (T32E.G (t - 36)) (m6 (T32E.G (t - 36)) i32))))

@[expose] noncomputable def witK (z a b : Nat) : Bool :=
  bIf(cm6 a b, bIf(Nat.beq a z, true, bIf(Nat.beq b z, true, bIf(Nat.beq b a, true,
    bIf(Nat.beq b (m6 a z), true,
      bIf(allN 42 (fun t => bAnd(cm6 (wW t) a, cm6 (wW t) b)), false, true))))), true)

@[expose] noncomputable def eK (e z i : Nat) : Bool :=
  strictB (T32E.T i) fun t => bIf(cm6 t e, true, Nat.beq (m6 t e) (m6 (m6 e z) t))

@[expose] noncomputable def eP : Nat := List.getD ezP 0 0

@[expose] noncomputable def zP : Nat := List.getD ezP 1 0

@[expose] noncomputable def tOK : Bool :=
  bAnd(allN 512 (invK dP), bAnd(allN 7 (fun a => allN 7 fun b =>
      witK zP (List.getD dP a 0) (List.getD dP b 0)),
    bAnd(allN 512 (eK eP zP), bAnd(Nat.beq (T32E.T (List.getD ePos 0 0)) eP,
    bAnd(Nat.beq (m6 eP eP) i32, bAnd(bIf(Nat.beq eP i32, false, true),
      bIf(Nat.beq eP zP, false, true)))))))

@[expose] noncomputable def bindOK : Bool :=
  bAnd(Nat.beq dP.length 7,
  bAnd(allN 7 (fun i => bAnd(bindArrK
      CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK.onKD[i]! 32 6 (List.getD dP i 0),
    permOK 32 6 (mask 6) (32 * 6) (List.getD dP i 0) (List.getD dP i 0))),
  bAnd(bindArrK CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK.onKE 32 6 eP,
  bAnd(bindArrK Data.T32z 32 6 zP,
  bAnd(bindArrK CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK.onKY5 120 7 y5,
    bindArrK CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK.onKY7 120 7 y7)))))

end CertificateChecks.KernelSpor.ONKL

end
