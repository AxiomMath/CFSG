module

public import Certificates.Kernel.Sporadic.OddCore.MNSl
public import Certificates.Data.Kernel.Spor.MulHF

public section

namespace CertificateChecks.KernelSpor.MNd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def hsPF (cnt : Nat) (T HS HSI : Nat → Nat) : Nat → Bool :=
  hsortPtKF 275 9 (mask 9) cnt T HS HSI

@[expose] noncomputable def r1HF (s : Nat) : Bool :=
  slSl MN.R1.cnt (hsPF MN.R1.cnt MN.R1.T MN.R1.HS MN.R1.HSI) 1125 s
@[expose] noncomputable def r2HF (s : Nat) : Bool :=
  slSl MN.R2.cnt (hsPF MN.R2.cnt MN.R2.T MN.R2.HS MN.R2.HSI) 1050 s
@[expose] noncomputable def k1HF (s : Nat) : Bool :=
  slSl MN.K1.cnt (hsPF MN.K1.cnt MN.K1.T MN.K1.HS MN.K1.HSI) 1120 s
@[expose] noncomputable def q1bHF (s : Nat) : Bool :=
  slSl MN.Q1b.cnt (hsPF MN.Q1b.cnt MN.Q1b.T MN.Q1b.HS MN.Q1b.HSI) 2880 s
@[expose] noncomputable def q1cHF (s : Nat) : Bool :=
  slSl MN.Q1c.cnt (hsPF MN.Q1c.cnt MN.Q1c.T MN.Q1c.HS MN.Q1c.HSI) 2880 s

end CertificateChecks.KernelSpor.MNd

end
