module

public import Certificates.Data.Kernel.ConjRec
public import Certificates.Kernel.U42Ten.Data

public section

namespace CertificateChecks.KernelU42Ten

open CFSG.KC.Enum CFSG.KC.ConjRec

@[expose] noncomputable def ok26121 (i : Nat) : Bool :=
  okO (nat_lit 45) (nat_lit 6) (nat_lit 270) (nat_lit 12) X XI Y YI Y T N i

theorem ch26121N : N = 2593 := by decide +kernel

theorem ch26121b0 : allBlk (nat_lit 0) ok26121 (nat_lit 325) = true := by decide +kernel
theorem ch26121b1 : allBlk (nat_lit 325) ok26121 (nat_lit 325) = true := by decide +kernel
theorem ch26121b2 : allBlk (nat_lit 650) ok26121 (nat_lit 325) = true := by decide +kernel
theorem ch26121b3 : allBlk (nat_lit 975) ok26121 (nat_lit 325) = true := by decide +kernel
theorem ch26121b4 : allBlk (nat_lit 1300) ok26121 (nat_lit 325) = true := by decide +kernel
theorem ch26121b5 : allBlk (nat_lit 1625) ok26121 (nat_lit 325) = true := by decide +kernel
theorem ch26121b6 : allBlk (nat_lit 1950) ok26121 (nat_lit 325) = true := by decide +kernel
theorem ch26121b7 : allBlk (nat_lit 2275) ok26121 (nat_lit 318) = true := by decide +kernel

end CertificateChecks.KernelU42Ten
