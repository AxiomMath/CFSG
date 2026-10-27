module

public import Certificates.Kernel.Misc.Perm.HS100.Base
public import Certificates.Kernel.Misc.Perm.HS100.S0Checks
public import Certificates.Data.Inputs256cGen5
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.G5

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.S0 (cK)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c

@[expose] noncomputable def GG (j : Nat) : Nat := if j = 0 then HX.F 0 else HX.F 1

@[expose] noncomputable def prodK (G : Nat → Nat) (w : List Nat) : Nat :=
  w.foldr (fun j acc => pcomp 100 7 (mask 7) (G j) acc) (pidn 100 7)

@[expose] noncomputable def powK (t : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 100 7) (fun _ acc => pcomp 100 7 (mask 7) t acc) k

@[expose] noncomputable def pNK (e₁ e₂ : Nat) (ab : Nat × Nat) : Nat :=
  pcomp 100 7 (mask 7) (powK e₁ ab.1) (powK e₂ ab.2)

@[expose] noncomputable def E1 : Nat := prodK GG hsG5E1W

@[expose] noncomputable def E2 : Nat := prodK GG hsG5E2W

@[expose] noncomputable def WK (i : Nat) : Nat := prodK GG (hsG5WW.getD i [])

theorem letters : ((hsG5E1W ++ hsG5E2W).all (fun j => decide (j < 2)) &&
    (hsG5Cls.all fun t => t.2.2.2.all (fun j => decide (j < 2)) && (t.2.2.1 == 1 || t.2.2.1 == 2)) &&
    hsG5Cls.map (fun t => (t.1, t.2.1)) == e9Pairs &&
    (hsG5WW.all fun w => w.all fun j => decide (j < 2)) && hsG5WP.length == hsG5WW.length &&
    (hsG5AW ++ hsG5BW).all (fun j => decide (j < hsG5WW.length)) && hsG5WW.length == 2) = true := by
  decide +kernel

theorem e9 : (Nat.beq (powK E1 3) (pidn 100 7) && Nat.beq (powK E2 3) (pidn 100 7) && cK E1 E2 &&
    !(Nat.beq E1 (pidn 100 7)) && !(Nat.beq E2 (pidn 100 7)) && !(Nat.beq E2 E1) &&
    !(Nat.beq E2 (powK E1 2))) = true := by quickRfl

theorem cls : (hsG5Cls.all fun t => Nat.beq (pcomp 100 7 (mask 7) (prodK GG t.2.2.2) (powK E1 t.2.2.1))
    (pcomp 100 7 (mask 7) (pNK E1 E2 (t.1, t.2.1)) (prodK GG t.2.2.2))) = true := by quickRfl

theorem sig : allN 2 (fun i => Nat.beq (powK (WK i) 5) (pidn 100 7) &&
    cK (WK i) (pNK E1 E2 (hsG5WP.getD i (0, 0))) &&
    !(Nat.beq (pNK E1 E2 (hsG5WP.getD i (0, 0))) (pidn 100 7))) = true := by quickRfl

theorem words : (Nat.beq (prodK WK hsG5AW) (HX.F 0) && Nat.beq (prodK WK hsG5BW) (HX.F 1)) = true := by
  quickRfl

end CertificateChecks.KernelMisc.HS100.G5

end
