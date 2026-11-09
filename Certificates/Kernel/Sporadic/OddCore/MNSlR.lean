module

public import Certificates.Kernel.Sporadic.OddCore.MNSl
public import Certificates.Data.Kernel.Spor.PEnumR

public section

namespace CertificateChecks.KernelSpor.MNd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnumR

@[expose] noncomputable def k1P (s : Nat) : Bool :=
  slSl MN.K1.cnt (penumPtR 275 9 (mask 9) MN.K1.GI 2 MN.K1.cnt MN.K1.T MN.K1.PL MN.K1.POS
    MN.K1.SRT MN.K1.SRI) 420 s

end CertificateChecks.KernelSpor.MNd

end
