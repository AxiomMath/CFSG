module

public import Certificates.Kernel.HSStd.U43VbR
public import Certificates.Data.Kernel.Spor.MulHC
public import Certificates.Data.Kernel.Spor.MulHF
public import Certificates.Data.Kernel.Spor.PEnumR
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelHSStd

@[expose] noncomputable def peCR (s : Nat) : Bool :=
  slK VbC.cnt (CFSG.KS.PEnumR.penumPtR 820 10 (mask 10) VbC.GI 5 VbC.cnt VbC.T VbC.PL VbC.POS
    VbC.SRT VbC.SRI) (Nat.mul 96 s) 96

@[expose] noncomputable def hsCF (s : Nat) : Bool :=
  slK VbC.cnt (hsortPtKF 820 10 (mask 10) VbC.cnt VbC.T VbC.HS VbC.HSI) (Nat.mul 288 s) 288

@[expose] noncomputable def clCR (s : Nat) : Bool :=
  slK (Nat.mul VbC.cnt 10) (clRK 5 10 VbC.cnt VbC.T VbC.POS
    (prodQK 820 10 (mask 10) 10 VbC.T (bothK 5 VbC.GI GJC)) VbCCl) (Nat.mul 960 s) 960

@[expose] noncomputable def peYR (s : Nat) : Bool :=
  slK VbY.cnt (CFSG.KS.PEnumR.penumPtR 820 10 (mask 10) VbY.GI 2 VbY.cnt VbY.T VbY.PL VbY.POS
    VbY.SRT VbY.SRI) (Nat.mul 81 s) 81

@[expose] noncomputable def hsYF (s : Nat) : Bool :=
  slK VbY.cnt (hsortPtKF 820 10 (mask 10) VbY.cnt VbY.T VbY.HS VbY.HSI) (Nat.mul 243 s) 243

@[expose] noncomputable def clYR (s : Nat) : Bool :=
  slK (Nat.mul VbY.cnt 4) (clRK 2 4 VbY.cnt VbY.T VbY.POS
    (prodQK 820 10 (mask 10) 4 VbY.T (bothK 2 VbY.GI GJY)) VbYCl) (Nat.mul 972 s) 972

end CertificateChecks.KernelHSStd.U43Vb

#kc_each CertificateChecks.KernelHSStd.U43Vb.peCR 0 30
#kc_each CertificateChecks.KernelHSStd.U43Vb.hsCF 0 10
#kc_each CertificateChecks.KernelHSStd.U43Vb.clCR 0 30
#kc_each CertificateChecks.KernelHSStd.U43Vb.peYR 0 24
#kc_each CertificateChecks.KernelHSStd.U43Vb.hsYF 0 8
#kc_each CertificateChecks.KernelHSStd.U43Vb.clYR 0 8

end
