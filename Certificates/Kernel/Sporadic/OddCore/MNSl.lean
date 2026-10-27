module

public import Certificates.Kernel.Sporadic.OddCore.MNK

public section

namespace CertificateChecks.KernelSpor.MNd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def peSl (k cnt : Nat) (G GI T PL POS SRT SRI : Nat → Nat) (L s : Nat) :
    Bool :=
  penumSlK 275 9 (mask 9) (275 * 9) true G GI k cnt T PL POS SRT SRI (Nat.mul L s) L

@[expose] noncomputable def slSl (cnt : Nat) (P : Nat → Bool) (L s : Nat) : Bool :=
  slK cnt P (Nat.mul L s) L

@[expose] noncomputable def hsP (cnt : Nat) (T HS HSI : Nat → Nat) : Nat → Bool :=
  hsortPtK 275 9 (mask 9) cnt T HS HSI

@[expose] noncomputable def r1E (s : Nat) : Bool :=
  peSl 2 MN.R1.cnt MN.R1.G MN.R1.GI MN.R1.T MN.R1.PL MN.R1.POS MN.R1.SRT MN.R1.SRI 450 s
@[expose] noncomputable def r1H (s : Nat) : Bool :=
  slSl MN.R1.cnt (hsP MN.R1.cnt MN.R1.T MN.R1.HS MN.R1.HSI) 1125 s
@[expose] noncomputable def r2E (s : Nat) : Bool :=
  peSl 2 MN.R2.cnt MN.R2.G MN.R2.GI MN.R2.T MN.R2.PL MN.R2.POS MN.R2.SRT MN.R2.SRI 420 s
@[expose] noncomputable def r2H (s : Nat) : Bool :=
  slSl MN.R2.cnt (hsP MN.R2.cnt MN.R2.T MN.R2.HS MN.R2.HSI) 1050 s
@[expose] noncomputable def k1E (s : Nat) : Bool :=
  peSl 2 MN.K1.cnt MN.K1.G MN.K1.GI MN.K1.T MN.K1.PL MN.K1.POS MN.K1.SRT MN.K1.SRI 420 s
@[expose] noncomputable def k1H (s : Nat) : Bool :=
  slSl MN.K1.cnt (hsP MN.K1.cnt MN.K1.T MN.K1.HS MN.K1.HSI) 1120 s
@[expose] noncomputable def k2E (s : Nat) : Bool :=
  peSl 4 MN.K2.cnt MN.K2.G MN.K2.GI MN.K2.T MN.K2.PL MN.K2.POS MN.K2.SRT MN.K2.SRI 300 s
@[expose] noncomputable def k2H (s : Nat) : Bool :=
  slSl MN.K2.cnt (hsP MN.K2.cnt MN.K2.T MN.K2.HS MN.K2.HSI) 2000 s
@[expose] noncomputable def syE (s : Nat) : Bool :=
  peSl 3 MN.SY.cnt MN.SY.G MN.SY.GI MN.SY.T MN.SY.PL MN.SY.POS MN.SY.SRT MN.SY.SRI 256 s
@[expose] noncomputable def syH (s : Nat) : Bool :=
  slSl MN.SY.cnt (hsP MN.SY.cnt MN.SY.T MN.SY.HS MN.SY.HSI) 256 s

@[expose] noncomputable def q1aE (s : Nat) : Bool :=
  peSl 2 MN.Q1a.cnt MN.Q1a.G MN.Q1a.GI MN.Q1a.T MN.Q1a.PL MN.Q1a.POS MN.Q1a.SRT MN.Q1a.SRI 450 s
@[expose] noncomputable def q1aH (s : Nat) : Bool :=
  slSl MN.Q1a.cnt (hsP MN.Q1a.cnt MN.Q1a.T MN.Q1a.HS MN.Q1a.HSI) 112 s
@[expose] noncomputable def q1bE (s : Nat) : Bool :=
  peSl 2 MN.Q1b.cnt MN.Q1b.G MN.Q1b.GI MN.Q1b.T MN.Q1b.PL MN.Q1b.POS MN.Q1b.SRT MN.Q1b.SRI 450 s
@[expose] noncomputable def q1bH (s : Nat) : Bool :=
  slSl MN.Q1b.cnt (hsP MN.Q1b.cnt MN.Q1b.T MN.Q1b.HS MN.Q1b.HSI) 2880 s
@[expose] noncomputable def q1cE (s : Nat) : Bool :=
  peSl 2 MN.Q1c.cnt MN.Q1c.G MN.Q1c.GI MN.Q1c.T MN.Q1c.PL MN.Q1c.POS MN.Q1c.SRT MN.Q1c.SRI 450 s
@[expose] noncomputable def q1cH (s : Nat) : Bool :=
  slSl MN.Q1c.cnt (hsP MN.Q1c.cnt MN.Q1c.T MN.Q1c.HS MN.Q1c.HSI) 2880 s
@[expose] noncomputable def q1dE (s : Nat) : Bool :=
  peSl 2 MN.Q1d.cnt MN.Q1d.G MN.Q1d.GI MN.Q1d.T MN.Q1d.PL MN.Q1d.POS MN.Q1d.SRT MN.Q1d.SRI 450 s
@[expose] noncomputable def q1dH (s : Nat) : Bool :=
  slSl MN.Q1d.cnt (hsP MN.Q1d.cnt MN.Q1d.T MN.Q1d.HS MN.Q1d.HSI) 1344 s
@[expose] noncomputable def q1eE (s : Nat) : Bool :=
  peSl 2 MN.Q1e.cnt MN.Q1e.G MN.Q1e.GI MN.Q1e.T MN.Q1e.PL MN.Q1e.POS MN.Q1e.SRT MN.Q1e.SRI 450 s
@[expose] noncomputable def q1eH (s : Nat) : Bool :=
  slSl MN.Q1e.cnt (hsP MN.Q1e.cnt MN.Q1e.T MN.Q1e.HS MN.Q1e.HSI) 1120 s
@[expose] noncomputable def q2aE (s : Nat) : Bool :=
  peSl 4 MN.Q2a.cnt MN.Q2a.G MN.Q2a.GI MN.Q2a.T MN.Q2a.PL MN.Q2a.POS MN.Q2a.SRT MN.Q2a.SRI 450 s
@[expose] noncomputable def q2aH (s : Nat) : Bool :=
  slSl MN.Q2a.cnt (hsP MN.Q2a.cnt MN.Q2a.T MN.Q2a.HS MN.Q2a.HSI) 1584 s
@[expose] noncomputable def q2bE (s : Nat) : Bool :=
  peSl 4 MN.Q2b.cnt MN.Q2b.G MN.Q2b.GI MN.Q2b.T MN.Q2b.PL MN.Q2b.POS MN.Q2b.SRT MN.Q2b.SRI 450 s
@[expose] noncomputable def q2bH (s : Nat) : Bool :=
  slSl MN.Q2b.cnt (hsP MN.Q2b.cnt MN.Q2b.T MN.Q2b.HS MN.Q2b.HSI) 720 s
@[expose] noncomputable def q2cE (s : Nat) : Bool :=
  peSl 4 MN.Q2c.cnt MN.Q2c.G MN.Q2c.GI MN.Q2c.T MN.Q2c.PL MN.Q2c.POS MN.Q2c.SRT MN.Q2c.SRI 450 s
@[expose] noncomputable def q2cH (s : Nat) : Bool :=
  slSl MN.Q2c.cnt (hsP MN.Q2c.cnt MN.Q2c.T MN.Q2c.HS MN.Q2c.HSI) 720 s
@[expose] noncomputable def q2dE (s : Nat) : Bool :=
  peSl 4 MN.Q2d.cnt MN.Q2d.G MN.Q2d.GI MN.Q2d.T MN.Q2d.PL MN.Q2d.POS MN.Q2d.SRT MN.Q2d.SRI 450 s
@[expose] noncomputable def q2dH (s : Nat) : Bool :=
  slSl MN.Q2d.cnt (hsP MN.Q2d.cnt MN.Q2d.T MN.Q2d.HS MN.Q2d.HSI) 440 s

@[expose] noncomputable def sel1S (s : Nat) : Bool := slSl MN.K1.cnt sel1K 420 s
@[expose] noncomputable def sel2S (s : Nat) : Bool := slSl MN.K2.cnt sel2K 990 s

end CertificateChecks.KernelSpor.MNd

end
