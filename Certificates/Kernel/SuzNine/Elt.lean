module

public import Certificates.Kernel.SuzNine.Chk
public import Certificates.Data.Kernel.SuzNine.Orb
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

public section

namespace CertificateChecks.KernelSuzNine

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.SuzNine CFSG.KS.Raw

@[expose] noncomputable def pc (p q : Nat) : Nat := CFSG.KC.Enum.pcomp 1782 11 (CFSG.KS.mask 11) p q

@[expose] noncomputable def idP : Nat := CFSG.KC.Enum.pidn 1782 11

@[expose] noncomputable def hw (w : List Int) : Nat := wordK 1782 11 (CFSG.KS.mask 11) idP HG HG w

@[expose] noncomputable def posW (w : List Int) : Bool :=
  andB (lettersK 10 w) (allL (w.map CFSG.KS.Mathieu.icode) fun c => Nat.beq (Nat.land c 1) 0)

@[expose] noncomputable def fixL (L : List Nat) (P : Nat) : Bool :=
  allL L fun p => anyL L fun q => Nat.beq (fldK P p) q

@[expose] noncomputable def xyK (wx wy : List Int) : Bool :=
  andB (posW wx) (andB (posW wy) (letB (hw wx) fun x => letB (hw wy) fun y => letB (pc x x) fun x2 =>
    andB (Nat.beq (pc x x2) idP) (andB (Nat.beq (pc y (pc y y)) idP)
    (andB (Nat.beq (pc x y) (pc y x)) (andB (notB (Nat.beq x idP))
    (andB (notB (Nat.beq y idP)) (andB (notB (Nat.beq y x)) (andB (notB (Nat.beq y x2))
    (andB (fixL X0L x) (fixL X0L y))))))))))

@[expose] noncomputable def agK (wa wg : List Int) : Bool :=
  andB (posW wa) (andB (posW wg) (letB (hw wa) fun a => letB (hw wg) fun g => letB (pc a a) fun a2 =>
    andB (Nat.beq (pc a a2) idP) (andB (notB (Nat.beq a idP))
    (andB (Nat.beq (pc g a) (pc a2 g)) (andB (fixL X0L a) (fixL X3L a))))))

theorem xy_chk : xyK XW YW = true := by quickRfl

theorem ag_chk : agK AW GW = true := by quickRfl

end CertificateChecks.KernelSuzNine

end
