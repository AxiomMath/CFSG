module

public import Certificates.Kernel.SporSch.HeT.X2114
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Data.Kernel.KGC31PB
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.HeldMixedInvolution
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import Certificates.Data.HeldMixedInvolution
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHeMix

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.HeldB

meta def MG : Array (Array Nat) := Mixed.generatorIndices.map fun j => heInnerSigma1.getD j #[]

meta def MRL : List (Array Nat) := Mixed.mixedWords.map (evalW 42 MG)

end CertificateChecks.KernelHeMix

#lc_reps CertificateChecks.KernelHeMix.MR 6 CertificateChecks.KernelHeMix.MG
  CertificateChecks.KernelHeMix.MRL

namespace CertificateChecks.KernelHeMix

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CertificateChecks.KernelSporSch.HeX14

@[expose] noncomputable def TL : List (List Nat) := trPL 42 6 X1Q.LR X1Q.TR 6

@[expose] noncomputable def TA : List Nat := pfilterProducts 42 6 (fun _ => true) TL (pidn 42 6) []

@[expose] noncomputable def IL : List Nat := pfilterProducts 42 6 (pord 42 6 2) TL (pidn 42 6) []

@[expose] noncomputable def RP (i : Nat) : Nat := MR.E (lget MR.OFF i)

@[expose] noncomputable def cntC (i : Nat) : Nat :=
  CFSG.KC.J2Cover.cntL (fun t => Nat.beq (pcomp 42 6 (mask 6) (RP i) t)
    (pcomp 42 6 (mask 6) t (RP i))) TA

end CertificateChecks.KernelHeMix

end
