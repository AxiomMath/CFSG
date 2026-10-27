module

public import Certificates.Kernel.EvenBN.Lists
public import Certificates.Kernel.Sporadic.Tits.LocS
public import Certificates.Kernel.Sporadic.Tits.LocJ
public import Certificates.Kernel.SporSch.Tits.GenSurv
public import Certificates.Data.Kernel.SporSch.TitsCnt
meta import Certificates.Data.TitsAschbacherE32

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN.E32

meta def sInvsM : List (Array Nat) := Certificates.TitsAschbacherE32.sInvs ()

end CertificateChecks.KernelEvenBN.E32

#kst_surv CertificateChecks.KernelEvenBN.E32.SI 11 CFSG.Sporadic.Schreier.Tits.titsSLevels
  CertificateChecks.KernelEvenBN.E32.sInvsM

namespace CertificateChecks.KernelEvenBN.E32

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelEvenBN Certificates.TitsAschbacherE32

@[expose] noncomputable def invK (t0 t1 t2 t3 t4 : Nat) : Bool :=
  sqPts 1755 11 (mask 11) t0 t1 t2 t3 t4 && !eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4

@[expose] noncomputable def QI : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ invK SI.M

@[expose] noncomputable def sS (X : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsS.LR TitsS.TRI TitsS.BP 5 0 X

@[expose] noncomputable def sJ (X : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0 X

@[expose] noncomputable def commP (A B : Nat) : Bool := baseComm TitsS.BP 5 (pgR A) (pgR B)

@[expose] noncomputable def XL : List (List Nat) := xkData.map xkL

@[expose] noncomputable def pivK (A : Nat) : Bool :=
  EL.any (Nat.beq A) || XL.any fun xs =>
    (SI.L.filter fun B => commP A B && (!sJ A || sJ B)).all fun B => xs.any (Nat.beq B)

end CertificateChecks.KernelEvenBN.E32

end
