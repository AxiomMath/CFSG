module

public import CFSG.Certificates.Kernel.Enum.ZCH
public import Certificates.Kernel.HSZC.Data

public section

namespace CertificateChecks.HSZCK

open CFSG.KC.Enum CFSG.KD.HSZC

theorem h_enum : hRange HT 0 0 0 RH 100 7 127 700 PM NH IDN (zP 1) H2 5 rep 168 = true := by
  decide +kernel
theorem h_reps : allN 5 (fun i => Nat.blt (rep i) NH) = true := by decide +kernel
theorem h_nc1 : allN 5 (fun i => ncOK HT 0 0 0 RH 100 7 127 700 PM NH (zP 1) i
    (List.getD NC1 i [])) = true := by decide +kernel
theorem h_nc2 : allN 5 (fun i => ncOK HT 0 0 0 RH 100 7 127 700 PM NH H2 i
    (List.getD NC2 i [])) = true := by decide +kernel
theorem h_k3 : eq3 100 7 127 IDN (rperm HT 0 0 0 RH PM K3) (rperm HT 0 0 0 RH PM K3)
    (rperm HT 0 0 0 RH PM K3) = true := by decide +kernel
theorem h_k3_ne : Nat.beq (pg 7 127 (rperm HT 0 0 0 RH PM K3) K3P) K3P = false := by
  decide +kernel
theorem h_k3_lt : bAnd(Nat.blt K3 NH, Nat.blt K3P 100) = true := by decide +kernel

end CertificateChecks.HSZCK

end
