module

public import Certificates.Kernel.LyGlue.Hex
public import Certificates.Data.Kernel.LyBase.Check

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.KC.LyBase CFSG.KC.LyGlue CertificateChecks.KernelLy

@[expose] noncomputable def cdEq (u v : List Int) : Bool :=
  andB (Nat.beq (cdPtC cL dL (u.map lcode) 0) (cdPtC cL dL (v.map lcode) 0))
    (andB (Nat.beq (cdPtC cL dL (u.map lcode) 3) (cdPtC cL dL (v.map lcode) 3))
      (Nat.beq (cdPtC cL dL (u.map lcode) 1) (cdPtC cL dL (v.map lcode) 1)))

end CertificateChecks.KernelLyModel

end
