module

public import Certificates.Kernel.J2Cover.ModelsP
public import Certificates.Kernel.LocalComp.J2Disp
public import Certificates.Kernel.LocalComp.BlockGen

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.DecText
open CFSG.ComponentClassification.J2Cover.Models

@[expose] def fusionBitF (aC fP fI : Nat → Nat) (fR : Array Nat) (i : Nat) : Bool :=
  let s := aC i
  let si := invTab[s]!
  let p := fP i
  let bp := betaTab[p]!
  bitAt fR si s ^^ lamBit p ^^ bitAt fR si bp ^^ bitAt fR ((mulTab[si]!)[bp]!) (aC (fI i))

@[expose] noncomputable def xorR (p : Nat → Bool) (lo len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun l ih => Bool.xor ih (p (Nat.add lo l))) len

end CertificateChecks.KernelJ2Cover

end
