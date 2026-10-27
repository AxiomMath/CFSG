module

public import Certificates.Kernel.HSStd.U43Z4Data
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.MulHC
public import Certificates.Data.Kernel.Spor.MulHF
public import Certificates.Data.Kernel.Spor.PEnumR
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CertificateChecks.KernelHSStd

@[expose] noncomputable def peC (s : Nat) : Bool :=
  slK Z4C.cnt (CFSG.KS.PEnumR.penumPtR 820 10 (mask 10) Z4C.GI 4 Z4C.cnt Z4C.T Z4C.PL Z4C.POS
    Z4C.SRT Z4C.SRI) (Nat.mul 96 s) 96

@[expose] noncomputable def hsC (s : Nat) : Bool :=
  slK Z4C.cnt (hsortPtKF 820 10 (mask 10) Z4C.cnt Z4C.T Z4C.HS Z4C.HSI) (Nat.mul 288 s) 288

@[expose] noncomputable def GJC (j : Nat) : Nat := Z4I (Nat.add j 2)

@[expose] noncomputable def clCs (s : Nat) : Bool :=
  slK (Nat.mul Z4C.cnt 8) (clRK 4 8 Z4C.cnt Z4C.T Z4C.POS
    (prodQK 820 10 (mask 10) 8 Z4C.T (bothK 4 Z4C.GI GJC)) Z4CCl) (Nat.mul 960 s) 960

@[expose] noncomputable def peY (s : Nat) : Bool :=
  slK Z4Y.cnt (CFSG.KS.PEnumR.penumPtR 820 10 (mask 10) Z4Y.GI 2 Z4Y.cnt Z4Y.T Z4Y.PL Z4Y.POS
    Z4Y.SRT Z4Y.SRI) (Nat.mul 81 s) 81

@[expose] noncomputable def hsY (s : Nat) : Bool :=
  slK Z4Y.cnt (hsortPtKF 820 10 (mask 10) Z4Y.cnt Z4Y.T Z4Y.HS Z4Y.HSI) (Nat.mul 243 s) 243

@[expose] noncomputable def GJY (j : Nat) : Nat := Z4I (Nat.add j 6)

@[expose] noncomputable def clYs (s : Nat) : Bool :=
  slK (Nat.mul Z4Y.cnt 4) (clRK 2 4 Z4Y.cnt Z4Y.T Z4Y.POS
    (prodQK 820 10 (mask 10) 4 Z4Y.T (bothK 2 Z4Y.GI GJY)) Z4YCl) (Nat.mul 972 s) 972

end CertificateChecks.KernelHSStd.U43Z4

#kc_each CertificateChecks.KernelHSStd.U43Z4.peC 0 30
#kc_each CertificateChecks.KernelHSStd.U43Z4.hsC 0 10
#kc_each CertificateChecks.KernelHSStd.U43Z4.clCs 0 24
#kc_each CertificateChecks.KernelHSStd.U43Z4.peY 0 24
#kc_each CertificateChecks.KernelHSStd.U43Z4.hsY 0 8
#kc_each CertificateChecks.KernelHSStd.U43Z4.clYs 0 8

end
