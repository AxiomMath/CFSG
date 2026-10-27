module

public import Certificates.Kernel.LocalComp.ExcU6.Data2
public import Certificates.Kernel.LocalComp.ExcU6.Data3
public import Certificates.Kernel.LocalComp.ExcU6.DataS
public import Certificates.Kernel.LocalComp.ExcU6.Derivs

public section

namespace CertificateChecks.KernelLC.ExcU6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.LocalComp.ExcDeriv

@[expose] noncomputable def ALIk (j : Nat) : Nat := pinvS 693 10 (mask 10) (lget ALL j)

@[expose] noncomputable def dOK (X : Nat) (E : Nat → Nat) (F : List Nat)
    (ds : List (List (ℕ × List ℤ × ℕ))) (i : Nat) : Bool :=
  bIf(Nat.beq (E i) X, true,
    derivSqK 693 10 (mask 10) (693 * 10) (pidn 693 10) (lget ALL) ALIk 64 F (ds.getD i [])
      [X, E i])

@[expose] noncomputable def dl1 (s : Nat) : Bool :=
  allBlk (Nat.mul 4 s) (fun i => bIf(Nat.blt i 43,
    dOK J1 (fun i => RS.E (lget RS.OFF i)) [] (decDerivs D.d1) i, true)) 4

@[expose] noncomputable def dl2 (s : Nat) : Bool :=
  allBlk (Nat.mul 4 s) (fun i => bIf(Nat.blt i 57,
    dOK X2 (fun i => R2.E (lget R2.OFF i)) [181] (decDerivs D.d2) i, true)) 4

@[expose] noncomputable def dl3 (s : Nat) : Bool :=
  allBlk (Nat.mul 4 s) (fun i => bIf(Nat.blt i 75,
    dOK X3 (fun i => R3.E (lget R3.OFF i)) [181, 53] (decDerivs D.d3) i, true)) 4

end CertificateChecks.KernelLC.ExcU6

end
