module

public import Certificates.Kernel.HSStd.U43Z4Data

public section

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CertificateChecks.KernelHSStd

@[expose] noncomputable def peK (s : Nat) : Bool :=
  penumSlK 820 10 (mask 10) (820 * 10) true Z4KY.G Z4KY.GI 3 Z4KY.cnt Z4KY.T Z4KY.PL Z4KY.POS
    Z4KY.SRT Z4KY.SRI (Nat.mul 112 s) 112

@[expose] noncomputable def hsK (s : Nat) : Bool :=
  slK Z4KY.cnt (hsortPtK 820 10 (mask 10) Z4KY.cnt Z4KY.T Z4KY.HS Z4KY.HSI) (Nat.mul 840 s) 840

end CertificateChecks.KernelHSStd.U43Z4

end
