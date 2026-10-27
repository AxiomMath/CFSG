module

public import Certificates.Kernel.LocalComp.E8Tables
public import Certificates.Kernel.Om2K.OrbData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
public import Certificates.Data.Holder1711.Om2Data

public section

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CertificateChecks.KernelLC.E8 (RT NEG)

@[expose] noncomputable def pc2 (p q : Nat) : Nat := pcomp 240 8 (mask 8) p q

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 480 9 (mask 9) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 480 9 (mask 9) p

@[expose] noncomputable def pid : Nat := pidn 480 9

@[expose] noncomputable def okK (p : Nat) : Bool :=
  bAnd(canonK 480 9 (mask 9) (480 * 9) p, bAnd(permOK 480 9 (mask 9) (480 * 9) p (pinv p),
    canonK 480 9 (mask 9) (480 * 9) (pinv p)))

@[expose] noncomputable def wAK (w : List Nat) : Nat := w.foldr (fun r acc => pc2 (RT r) acc) (pidn 240 8)

@[expose] noncomputable def pairK (A B : Nat) : Nat :=
  pmk 480 9 fun i =>
    Bool.rec (motive := fun _ => Nat) (Nat.add (pg 8 255 B (Nat.sub i 240)) 240) (pg 8 255 A i)
      (Nat.blt i 240)

@[expose] noncomputable def gYK (i : Nat) : Nat :=
  pairK (wAK (CFSG.EvenSmallLie.OmegaEight.Weyl.omWords.getD i [])) (wAK (yW.getD i []))

@[expose] noncomputable def wYK (w : List Nat) : Nat := w.foldr (fun l acc => pc (L.G l) acc) pid

@[expose] noncomputable def cj (g y : Nat) : Nat := pc g (pc y (pinv g))

@[expose] def elW : List (List Nat) := [wT0, wI0, wJ0, wTc, wFuseC, wLiftA, wLiftB]

@[expose] noncomputable def q8K (x y : Nat) : List Nat :=
  [pid, x, pc x x, pc (pc x x) x, y, pc y x, pc y (pc x x), pc y (pc (pc x x) x)]

@[expose] noncomputable def cAK (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (pairK NEG NEG) (pairK (pidn 240 8) NEG) (Nat.beq k 1))
    (pairK NEG (pidn 240 8)) (Nat.beq k 0)

end CertificateChecks.KernelOm2

end
