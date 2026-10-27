module

public import Certificates.Data.Kernel.ThI301.Defs
public import Certificates.Kernel.ThI301.Data

public section

namespace CertificateChecks.ThI301K

open CFSG.KC.Enum CFSG.KC.ThI301 CFSG.KD.ThI301

theorem nL_eq : Nat.beq NL 2619 = true := by decide +kernel
theorem pm_eq : Nat.beq PM (Nat.sub (Nat.shiftLeft 1 36) 1) = true := by decide +kernel

theorem l_all : lRange IT 0 0 0 RO 9 4 15 36 PM 12 4095 NL A AI B BI 0 2619 = true := by
  decide +kernel
theorem th_all : thRange IT RO yP yPI 0 2619 = true := by
  decide +kernel

end CertificateChecks.ThI301K

end
