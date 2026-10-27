module

public import Certificates.Kernel.Sporadic.OddCore.SuzK0
public import Certificates.Data.Kernel.CentSub
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz786002

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KC.CentScan CFSG.KC.CentSub CertificateChecks.KernelSpor
open CFSG.KLie.CT (andB notB)

@[expose] noncomputable def mul (p q : Nat) : Nat := pcomp 42 6 (mask 6) p q

@[expose] noncomputable def RA : Nat := SuzDP 4

@[expose] noncomputable def RB : Nat := mul (SuzDP 3) (mul (SuzDP 4) (SuzDP 3))

@[expose] noncomputable def DL : Nat := mul (SuzDP 4) (SuzDP 4)

@[expose] noncomputable def roots (a b : Nat) (j : Nat) : Nat := [a, b].getD j 0

@[expose] noncomputable def zs (e a b : Nat) (k : Nat) : Nat :=
  [e, mul a a, mul b b, mul (mul a a) (mul b b)].getD k 0

@[expose] noncomputable def RP : Nat → Nat := roots RA RB

@[expose] noncomputable def ZP : Nat → Nat := zs (pidn 42 6) RA RB

@[expose] noncomputable def rootOK (d e x : Nat) : Bool :=
  andB (commPt 42 6 x d) (Nat.beq (mul (mul x x) (mul x x)) e)

theorem kRoot : andB (rootOK DL (pidn 42 6) RA) (rootOK DL (pidn 42 6) RB) = true := by
  quickRfl

@[expose] noncomputable def ptOK (e a b v x : Nat) : Bool :=
  andB (centSubK 42 6 2 (roots a b) 4 (zs e a b) x) (offK 42 6 2 (roots a b) v x)

@[expose] noncomputable def scSl (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB RA fun a => strictB RB fun b => strictB (SuzSV 0) fun v =>
    scanSl (ptOK e a b v) SK0.T 1260 s

theorem kNeg : andB (notB (centSubK 42 6 2 RP 3 ZP (ZP 3)))
    (andB (notB (centSubK 42 6 2 (roots (pidn 42 6) (pidn 42 6)) 4 ZP (SuzDP 0)))
      (andB (notB (offK 42 6 2 RP (pidn 42 6) (pidn 42 6)))
        (andB (notB (rootOK DL (pidn 42 6) (SuzDP 0))) (notB (rootOK DL RB RB))))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Suz786002

end
