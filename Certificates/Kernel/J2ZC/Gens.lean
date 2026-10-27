module

public import CFSG.Certificates.Kernel.Enum.ZChk
public import Certificates.Kernel.J2ZC.Data

public section

namespace CertificateChecks.J2ZCK

open CFSG.KC.Enum CFSG.KD.J2ZC

theorem idn_eq : Nat.beq IDN (pidn 315 9) = true := by decide +kernel
theorem z_ab : eq2 315 9 511 (zP 1) A B = true := by decide +kernel
theorem z_pow : zPowOK 315 9 511 2835 (zP 1) zP zPI 3 = true := by decide +kernel
theorem syl_gens :
    allN 3 (fun j => Nat.beq (gS j) (wperm 315 9 511 A B AI BI (wS j) (lS j))) = true := by
  decide +kernel
theorem nL_eq : Nat.beq NL 2835 = true := by decide +kernel
theorem nS_eq : Nat.beq NS 128 = true := by decide +kernel
theorem pm_eq : Nat.beq PM (Nat.sub (Nat.shiftLeft 1 2835) 1) = true := by decide +kernel

end CertificateChecks.J2ZCK

end
