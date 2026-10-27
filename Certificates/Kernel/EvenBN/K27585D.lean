module

public import Certificates.Kernel.EvenBN.DWord
public import Certificates.Kernel.EvenBN.Bind
public import Certificates.Data.TitsAschbacherFive

public section

namespace CertificateChecks.KernelEvenBN.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherFive Certificates.MaxD2Perm

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def X : Nat := wP TitsH.S hatXWord

@[expose] noncomputable def U2 : Nat := wP TitsH.S u2Word

@[expose] noncomputable def Hd : Nat := wP TitsH.S deltaHWord

@[expose] noncomputable def Dl : Nat :=
  pc (pc Hd (ppw (pc (wTP deltaAWord) CertificateChecks.KernelSporSch.TitsZ) 2)) (wTP deltaBWord)

end CertificateChecks.KernelEvenBN.Five

end
