module

public import Certificates.Kernel.LocalComp.L34Para.Data
public import Certificates.Data.Kernel.L34Pow
public import Certificates.Data.Kernel.L34W.Tab42

public section

namespace CertificateChecks.KernelLC.L34T3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KC.L34W CFSG.KC.L34Pow CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def centPt (z0 z4 z8 z12 x : Nat) : Bool :=
  orB (notB (allN 4 fun j => commPt 42 6 x (L34PT.G j)))
    (orB (Nat.beq x z0) (orB (Nat.beq x z4) (orB (Nat.beq x z8) (Nat.beq x z12))))

@[expose] noncomputable def cent22211 (s : Nat) : Bool :=
  strictB (L34PT.T 0) fun z0 => strictB (L34PT.T 5) fun z4 =>
    strictB (L34PT.T 60) fun z8 => strictB (L34PT.T 51) fun z12 =>
      scanSl (centPt z0 z4 z8 z12) L34R.T 1344 s

@[expose] noncomputable def chunk45 (F : Nat → Bool) (j : Nat) : Bool :=
  allN 45 fun t => F (Nat.add (Nat.mul 45 j) t)

end CertificateChecks.KernelLC.L34T3

end
