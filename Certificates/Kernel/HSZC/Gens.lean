module

public import CFSG.Certificates.Kernel.Enum.ZChk
public import Certificates.Kernel.HSZC.Data

public section

namespace CertificateChecks.HSZCK

open CFSG.KC.Enum CFSG.KD.HSZC

theorem idn_eq : Nat.beq IDN (pidn 100 7) = true := by decide +kernel
theorem z_word : Nat.beq (zP 1) (wperm 100 7 127 A B AI BI ZW ZL) = true := by decide +kernel
theorem z_pow : zPowOK 100 7 127 700 (zP 1) zP zPI 8 = true := by decide +kernel
theorem z_seven : Nat.beq (zP 7) IDN = true := by decide +kernel
theorem z_ne : Nat.beq (pg 7 127 (zP 1) ZP) ZP = false := by decide +kernel
theorem zp_lt : Nat.blt ZP 100 = true := by decide +kernel
theorem h2_word : Nat.beq H2 (wperm 100 7 127 A B AI BI H2W H2L) = true := by decide +kernel
theorem h2_sq : eq2 100 7 127 IDN H2 H2 = true := by decide +kernel
theorem z_h2 : eq22 100 7 127 (zP 1) H2 H2 (zP 1) = false := by decide +kernel
theorem syl_gens :
    allN 3 (fun j => Nat.beq (gS j) (wperm 100 7 127 A B AI BI (wS j) (lS j))) = true := by
  decide +kernel
theorem nL_eq : Nat.beq NL 21175 = true := by decide +kernel
theorem nX_eq : Nat.beq NX 21161 = true := by decide +kernel
theorem nS_eq : Nat.beq NS 512 = true := by decide +kernel
theorem nH_eq : Nat.beq NH 168 = true := by decide +kernel
theorem pm_eq : Nat.beq PM (Nat.sub (Nat.shiftLeft 1 700) 1) = true := by decide +kernel

end CertificateChecks.HSZCK

end
