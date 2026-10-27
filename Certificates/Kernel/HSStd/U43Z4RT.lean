module

public import Certificates.Kernel.HSStd.U43Z4Data
public import Certificates.Data.Kernel.Spor.MulHQ
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CertificateChecks.KernelHSStd

@[expose] noncomputable def peT (s : Nat) : Bool :=
  penumSlK 820 10 (mask 10) (820 * 10) true Z4KT.G Z4KT.GI 3 Z4KT.cnt Z4KT.T Z4KT.PL Z4KT.POS
    Z4KT.SRT Z4KT.SRI (Nat.mul 126 s) 126

@[expose] noncomputable def hsT (s : Nat) : Bool :=
  slK Z4KT.cnt (hsortPtK 820 10 (mask 10) Z4KT.cnt Z4KT.T Z4KT.HS Z4KT.HSI) (Nat.mul 567 s) 567

end CertificateChecks.KernelHSStd.U43Z4

#kc_each CertificateChecks.KernelHSStd.U43Z4.peT 0 36
#kc_each CertificateChecks.KernelHSStd.U43Z4.hsT 0 8

end
