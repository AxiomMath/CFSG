module

public import Certificates.Kernel.Misc.Tits.Text
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelMisc

@[expose] noncomputable def DS (k : Nat) : Nat :=
  nIf(Nat.blt k 13, TitsText.F (18 + k), TitsText.F 18)

@[expose] noncomputable def DSI (k : Nat) : Nat := pinvS 1755 11 (mask 11) (DS k)

@[expose] noncomputable def GS (k : Nat) : Nat :=
  nIf(Nat.blt k 4, TitsText.F k, TitsText.F 0)

@[expose] noncomputable def GSI (k : Nat) : Nat := pinvS 1755 11 (mask 11) (GS k)

@[expose] noncomputable def WD (wd : List Int) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) DS DSI wd

@[expose] noncomputable def WG (wd : List Int) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) GS GSI wd

@[expose, reducible] noncomputable def pm (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose, reducible] noncomputable def pv (p : Nat) : Nat := pinvS 1755 11 (mask 11) p

@[expose, reducible] noncomputable def pe : Nat := pidn 1755 11

@[expose, reducible] noncomputable def ppw (p : Nat) (k : Nat) : Nat := ppow 1755 11 (mask 11) pe p k

theorem dPerm : allN 13 (fun k => permOK 1755 11 (mask 11) (1755 * 11) (DS k) (DSI k)) = true := by
  quickRfl

theorem gPerm : allN 4 (fun k => permOK 1755 11 (mask 11) (1755 * 11) (GS k) (GSI k)) = true := by
  quickRfl

theorem d0Canon : canonK 1755 11 (mask 11) (1755 * 11) (DS 0) = true := by quickRfl
theorem g0Canon : canonK 1755 11 (mask 11) (1755 * 11) (GS 0) = true := by quickRfl

end CertificateChecks.KernelTitsW

end
