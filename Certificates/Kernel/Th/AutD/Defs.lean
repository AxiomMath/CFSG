module

public import Certificates.Kernel.Th.AutD.Data
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Data.Kernel.L34K
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Th.S.Hsw

public section

namespace CertificateChecks.KernelTh.AutD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KS.PEnum CertificateChecks.KernelTh.AutDG CFSG.Sporadic.Th.Recog
open CFSG.KLie.CT (fget andB orB notB)

@[expose] noncomputable def pc (x y : Nat) : Nat := pcomp 51 6 (mask 6) x y

@[expose] noncomputable def pinv (x : Nat) : Nat := pinvS 51 6 (mask 6) x

@[expose] noncomputable def L (j : Nat) : Nat := ADE.G j

@[expose] noncomputable def LI (j : Nat) : Nat := pinv (ADE.G j)

@[expose] noncomputable def wK {m : Nat} (G GI : Nat → Nat) (w : List (Fin m × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 51 6)
    (fun l _ acc => pc (Bool.rec (motive := fun _ => Nat) (GI l.1.val) (G l.1.val) l.2) acc) w

@[expose] noncomputable def pw (x n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 51 6) (fun _ acc => pc x acc) n

@[expose] noncomputable def ord24K (x : Nat) : Bool :=
  andB (Nat.beq (pw x 24) (pidn 51 6)) (andB (notB (Nat.beq (pw x 12) (pidn 51 6)))
    (notB (Nat.beq (pw x 8) (pidn 51 6))))

@[expose] noncomputable def g2 (X Y j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) Y X (Nat.beq j 0)

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) l

@[expose] def decW : Nat → Nat → List (Fin 8 × Bool)
  | 0, _ => []
  | k + 1, m => (Fin.ofNat 8 (m % 256 / 2), m % 2 == 0) :: decW k (m / 256)

@[expose] def decE (n : Nat) : List (Fin 8 × Bool) := decW (n % 4096 / 4) (n / 4096)

@[expose] def rdC : List (List (Fin 6 × Bool)) :=
  CFSG.CosetTable.restrictWords dS (CFSG.KC.Th.Hsw.list.map decE)

@[expose] def autTestsC : List (List (Fin 2 × Bool)) :=
  (rdC ++ [duSix]).map
      (CFSG.CosetTable.substWord (List.ofFn lW)) ++
    List.ofFn fun i => CFSG.CosetTable.substWord (List.ofFn lW) (hW i) ++ [(i, false)]

@[expose] noncomputable def testK (X XI Y YI : Nat) : Bool :=
  allL autTestsC fun S => Nat.beq (wK (g2 X Y) (g2 XI YI) S) (pidn 51 6)

@[expose] noncomputable def H (i : Nat) : Nat := wK L LI (hW (Fin.ofNat 2 i))

@[expose] noncomputable def HI (i : Nat) : Nat := wK L LI (FreeGroup.invRev (hW (Fin.ofNat 2 i)))

@[expose] noncomputable def X1 : Nat := wK L LI x1W

@[expose] noncomputable def X1I : Nat := wK L LI (FreeGroup.invRev x1W)

@[expose] noncomputable def PI (k : Nat) : Nat := API k

@[expose] noncomputable def PII (k : Nat) : Nat := pinv (API k)

@[expose] noncomputable def tw (k i : Nat) : Nat := pc (pc (PI k) (H i)) (PII k)

@[expose] noncomputable def AW (d : Nat) : Nat :=
  fget (AWP (Nat.shiftRight d (nat_lit 4))) (Nat.land d (nat_lit 15)) (nat_lit 16)

@[expose] noncomputable def witK (w X Y : Nat) : Bool :=
  andB (Nat.blt 0 w) (strictB (Nat.shiftRight (Nat.sub w 1) 12) fun f =>
    strictB (Nat.land (Nat.sub w 1) 4095) fun m =>
      andB (Nat.blt f 8) (andB (Nat.blt m 3456) (strictB (ADE.T m) fun M =>
        strictB (pinv M) fun MI =>
          andB (Nat.beq (pc (pc M (tw f 0)) MI) X) (Nat.beq (pc (pc M (tw f 1)) MI) Y))))

@[expose] noncomputable def autK (i c : Nat) : Bool :=
  strictB (Bool.rec (motive := fun _ => Nat) X1 (H 0) (Nat.beq c 0)) fun X =>
  strictB (Bool.rec (motive := fun _ => Nat) X1I (HI 0) (Nat.beq c 0)) fun XI =>
  strictB (ADE.T i) fun Y => strictB (pinv Y) fun YI =>
    orB (notB (testK X XI Y YI)) (witK (AW (Nat.add (Nat.mul 2 i) c)) X Y)

@[expose] noncomputable def aSl (s : Nat) : Bool :=
  allN 128 fun d => strictB (Nat.add (Nat.mul 128 s) d) fun i => andB (autK i 0) (autK i 1)

@[expose] noncomputable def invK (i : Nat) : Bool :=
  strictB (ADE.T i) fun t => strictB (pinv t) fun ti =>
    andB (canonK 51 6 (mask 6) (51 * 6) ti)
      (andB (Nat.beq (pc t ti) (pidn 51 6)) (Nat.beq (pc ti t) (pidn 51 6)))

@[expose] noncomputable def inOA (x : Nat) : Bool := notB (allN 144 fun q => notB (Nat.beq (AOA.T q) x))

@[expose] noncomputable def inOB (x : Nat) : Bool := notB (allN 144 fun q => notB (Nat.beq (AOB.T q) x))

@[expose] noncomputable def pt (i : Nat) : Bool :=
  andB (invK i) (strictB (ADE.T i) fun t =>
    orB (notB (ord24K t)) (orB (inOA t) (inOB t)))

end CertificateChecks.KernelTh.AutD

end
