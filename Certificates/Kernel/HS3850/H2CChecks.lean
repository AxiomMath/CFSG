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

@[expose] noncomputable def X7 : Nat := pc (pc (HC.F 24) (HC.F 28)) (pinv (HC.F 24))

@[expose] noncomputable def X5 : Nat := pc (pc G5 (HC.F 26)) (pinv G5)

@[expose] noncomputable def pw (e P : Nat) : Nat := Nat.rec (motive := fun _ => Nat) idn
  (fun _ acc => pc P acc) e

@[expose] noncomputable def permK (P : Nat) : Bool :=
  canonK 3850 12 (mask 12) (3850 * 12) P &&
    canonK 3850 12 (mask 12) (3850 * 12) (pinv P) &&
    invEqK 3850 12 (mask 12) (3850 * 12) P (pinv P)

@[expose] noncomputable def ck7 (s : Nat) : Bool :=
  slK M7.cnt (fun i => penumPtTK 3850 12 (mask 12) (3850 * 12) true M7.G M7.GI 2 M7.cnt 200
    M7.T M7.PL M7.POS M7.SRT M7.SRI i && hsortPtK 3850 12 (mask 12) M7.cnt M7.T M7.HS M7.HSI i)
    (32 * s) 32

@[expose] noncomputable def ck5 (s : Nat) : Bool :=
  slK M5.cnt (fun i => penumPtTK 3850 12 (mask 12) (3850 * 12) true M5.G M5.GI 2 M5.cnt 400
    M5.T M5.PL M5.POS M5.SRT M5.SRI i && hsortPtK 3850 12 (mask 12) M5.cnt M5.T M5.HS M5.HSI i)
    (32 * s) 32

theorem small : (permK (HC.F 24) && permK G5 && permK X7 && permK X5 &&
    Nat.beq (wfoldR ls8 SW7) (HC.F 28) && Nat.beq (wfoldR ls8 SW5) (HC.F 26) &&
    Nat.beq (pc (HC.F 28) (HC.F 21)) (pc (HC.F 21) (HC.F 28)) &&
    Nat.beq (pc (HC.F 26) (HC.F 21)) (pc (HC.F 21) (HC.F 26)) &&
    Nat.beq (pw 7 (HC.F 28)) idn && Nat.beq (pw 5 (HC.F 26)) idn) = true := by quickRfl

theorem binds : (Nat.beq M7.k 2 && Nat.beq M7.cnt 347 && allN 2 (fun j => Nat.beq (M7.G j) idn) &&
    Nat.beq (M7.GI 0) (HC.F 28) && Nat.beq (M7.GI 1) X7 && penumHdTK idn M7.cnt M7.T M7.PL &&
    Nat.beq M5.k 2 && Nat.beq M5.cnt 732 && allN 2 (fun j => Nat.beq (M5.G j) idn) &&
    Nat.beq (M5.GI 0) (HC.F 26) && Nat.beq (M5.GI 1) X5 && penumHdTK idn M5.cnt M5.T M5.PL) =
    true := by quickRfl

end CertificateChecks.KernelHS3850.H2C

end

set_option maxRecDepth 400000

#kqb_range CertificateChecks.KernelHS3850.H2C.C7 CertificateChecks.KernelHS3850.H2C.ck7 0 11
#kqb_all CertificateChecks.KernelHS3850.H2C.C7 CertificateChecks.KernelHS3850.H2C.ck7 11
