module

public import Certificates.Data.Kernel.U43Twin.Psi
public import Certificates.Kernel.U43Twin.WData

public section

namespace CertificateChecks.KernelU43Twin

open CFSG.KC.Enum CFSG.KD.U43Pk CFSG.KD.U43Twin

@[expose] noncomputable def SQK (v : Nat) : Nat :=
  fld(232643254877787509568551519864953968568550956484623, Nat.mul 7 v, 127)

@[expose] noncomputable def MT (a b : Nat) : Nat := qposK SQK (qmK (SQK a) (SQK b))

@[expose] noncomputable def G0K : Nat := 3919932909454517859

@[expose] noncomputable def ch397503psi (a : Nat) : Bool := psiRowK L2 L1 MT (FX 45) (FX 48) a

end CertificateChecks.KernelU43Twin

end
