module

public import Certificates.Kernel.LyTr.Data

public section

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Raw

@[expose] noncomputable def r1Sl (s : Nat) : Bool :=
  penumSlK 1080 11 (mask 11) (1080 * 11) true R1.G R1.GI 5 R1.cnt R1.T R1.PL R1.POS R1.SRT R1.SRI
    (81 * s) 81

@[expose] noncomputable def r2Sl (s : Nat) : Bool :=
  penumSlK 243 8 (mask 8) (243 * 8) true R2.G R2.GI 5 R2.cnt R2.T R2.PL R2.POS R2.SRT R2.SRI
    (243 * s) 243

@[expose] noncomputable def r2clSl (s : Nat) : Bool :=
  slK (Nat.mul R2.cnt 10)
    (findPtK R2.cnt R2.T (prodQK 243 8 (mask 8) 10 R2.T (bothK 5 R2.GI R2I)) R2Cl)
    (2430 * s) 2430

end CertificateChecks.KernelLyTr

end
