module

public import Certificates.Kernel.HeLoc.FiveData
public import Certificates.Kernel.SporSch.HeT.Tab

public section

namespace CertificateChecks.KernelHeLoc

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def uM (x : Nat) : Nat := powF (pg 14 (mask 14) (Five.AR.F 0)) 5 x

@[expose] noncomputable def memAt (G F f x : Nat) : Bool :=
  bIf(Nat.blt x 8330,
    Nat.beq (nIf(Nat.beq f 0, pg 14 (mask 14) G x, pg 14 (mask 14) G (uM x))) (HeTc.nfp F x),
    true)

@[expose] noncomputable def memB (G F f c : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul 833 c) 833 (memAt G F f)

end CertificateChecks.KernelHeLoc

end
