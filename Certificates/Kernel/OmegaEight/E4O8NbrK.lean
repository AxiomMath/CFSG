module

public import Certificates.Kernel.OmegaEight.Om0Gen118003K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

@[expose] def e4UW : List Int :=
  CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 CFSG.ClassicalInvolution.Q3.TL4.E4O8Data.u0Word

@[expose] noncomputable def e4U : Nat := wO e4UW

@[expose] noncomputable def e4Q (r i j : Nat) : List Nat :=
  [pid, r, i, pc i r, j, pc j r, pc i j, pc (pc i j) r]

@[expose] noncomputable def e4L : List Nat := e4Q (mainK 0) e4U om0V

@[expose] noncomputable def e4Mem (L : List Nat) (x : Nat) : Bool := L.any (Nat.beq x)

@[expose] noncomputable def e4Norms (L : List Nat) (i j h : Nat) : Bool :=
  e4Mem L (cj h i) && e4Mem L (cj h j)

@[expose] noncomputable def e4Edge (L : List Nat) (i j g : Nat) : Bool :=
  !e4Norms L i j g && e4Norms L i j (cj g i) && e4Norms L i j (cj g j)

@[expose] noncomputable def e4Pm (p : Nat) : Bool := bAnd(pm p, cn (pinv p))

@[expose] noncomputable def e4EdgeAt (g : Nat) : Bool :=
  bAnd(e4Pm (cj g e4U), bAnd(e4Pm (cj g om0V), e4Edge e4L e4U om0V g))

@[expose] noncomputable def e4DiffAt (a b : Nat) : Bool :=
  bAnd(e4Pm (pc (pinv a) b), bIf(e4Norms e4L e4U om0V (pc (pinv a) b), false, true))

theorem kE4Nbr : bAnd(lettersK 17 e4UW, bAnd(cn e4U, bAnd(e4EdgeAt (AP.S 0),
    bAnd(e4EdgeAt (AP.S 4), bAnd(e4EdgeAt (AP.S 6), bAnd(e4DiffAt (AP.S 0) (AP.S 4),
    bAnd(e4DiffAt (AP.S 0) (AP.S 6), e4DiffAt (AP.S 4) (AP.S 6)))))))) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
