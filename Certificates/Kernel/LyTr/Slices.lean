module

public import Certificates.Kernel.LyTr.Data
public import Certificates.Data.Kernel.Spor.PEnumR

public section

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Raw

@[expose] noncomputable def r1Sl (s : Nat) : Bool :=
  slK R1.cnt (CFSG.KS.PEnumR.penumPtR 1080 11 (mask 11) R1.GI 5 R1.cnt R1.T R1.PL R1.POS R1.SRT
    R1.SRI) (81 * s) 81

@[expose] noncomputable def r2Sl (s : Nat) : Bool :=
  slK R2.cnt (CFSG.KS.PEnumR.penumPtR 243 8 (mask 8) R2.GI 5 R2.cnt R2.T R2.PL R2.POS R2.SRT
    R2.SRI) (243 * s) 243

end CertificateChecks.KernelLyTr

end
