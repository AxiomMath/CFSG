module

public import Certificates.Kernel.HS3850.H2CData
public import Certificates.Kernel.LocalQT.HSAut.K4146R
public import Certificates.Data.Kernel.Spor.PEnumT
public import Certificates.Data.Kernel.Spor.MulH
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS3850.H2C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.HN
open CFSG.KD.LQT.C4126 CFSG.KS.MulH

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 3850 12 (mask 12) p

@[expose] noncomputable def G5 : Nat := pc (HC.F 25) (HC.F 23)

@[expose] noncomputable def G7 : Nat := pc (HC.F 23) (HC.F 24)

@[expose] noncomputable def X7 : Nat := pc (pc G7 (HC.F 28)) (pinv G7)

@[expose] noncomputable def X5 : Nat := pc (pc G5 (HC.F 26)) (pinv G5)

@[expose] noncomputable def pw (e P : Nat) : Nat := Nat.rec (motive := fun _ => Nat) idn
  (fun _ acc => pc P acc) e

@[expose] noncomputable def permK (P : Nat) : Bool :=
  canonK 3850 12 (mask 12) (3850 * 12) P &&
    canonK 3850 12 (mask 12) (3850 * 12) (pinv P) &&
    invEqK 3850 12 (mask 12) (3850 * 12) P (pinv P)

@[expose] noncomputable def Z5 : Nat := pc (HC.F 26) X5

@[expose] noncomputable def Z7 : Nat := pc (HC.F 28) X7

@[expose] noncomputable def W7 : Nat := pw 3 Z7

theorem small : (permK G7 && permK G5 && permK X7 && permK X5 &&
    Nat.beq (wfoldR ls8 SW7) (HC.F 28) && Nat.beq (wfoldR ls8 SW5) (HC.F 26) &&
    Nat.beq (pc (HC.F 28) (HC.F 21)) (pc (HC.F 21) (HC.F 28)) &&
    Nat.beq (pc (HC.F 26) (HC.F 21)) (pc (HC.F 21) (HC.F 26)) &&
    Nat.beq (pw 7 (HC.F 28)) idn && Nat.beq (pw 5 (HC.F 26)) idn &&
    Nat.beq (pw 7 Z5) idn && !Nat.beq Z5 idn &&
    Nat.beq (pw 5 W7) idn && !Nat.beq W7 idn) = true := by quickRfl

end CertificateChecks.KernelHS3850.H2C

end
