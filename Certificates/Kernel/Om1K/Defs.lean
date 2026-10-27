module

public import Certificates.Kernel.Om2K.Defs
public import Certificates.Data.Holder1711.Om1Data

public section

namespace CertificateChecks.KernelOm1.A

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelOm2 (pc2 wAK)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data

@[expose] noncomputable def pid1 : Nat := pidn 240 8

@[expose] noncomputable def pinv1 (p : Nat) : Nat := pinvS 240 8 (mask 8) p

@[expose] noncomputable def okK2 (p : Nat) : Bool :=
  bAnd(canonK 240 8 (mask 8) (240 * 8) p, bAnd(permOK 240 8 (mask 8) (240 * 8) p (pinv1 p),
    canonK 240 8 (mask 8) (240 * 8) (pinv1 p)))

@[expose] noncomputable def genOK (ws : List (List Nat)) (G : Nat → Nat) (k : Nat) : Bool :=
  bAnd(Nat.beq (G k) (wAK (ws.getD k [])), okK2 (G k))

@[expose] noncomputable def cmK (x y : Nat) : Bool := Nat.beq (pc2 x y) (pc2 y x)

@[expose] noncomputable def q8L (x y : Nat) : List Nat :=
  [pid1, x, pc2 x x, pc2 (pc2 x x) x, y, pc2 y x, pc2 y (pc2 x x), pc2 y (pc2 (pc2 x x) x)]

@[expose] def elW : List (List Nat) := [wT0, wI0, wJ0, wS1, wG1, wS1.reverse]

@[expose] def k0W : List (List Nat) :=
  [wI0, wJ0, wS1 ++ wI0 ++ wS1.reverse, wS1 ++ wJ0 ++ wS1.reverse]

@[expose] def wXr : List (List Nat) := wX.map List.reverse

end CertificateChecks.KernelOm1.A

end
