module

public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Data.Kernel.Child3
public import Certificates.Kernel.J2Cover.Gens19
meta import Certificates.Kernel.J2Cover.Gens19
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#lc_reps CertificateChecks.KernelJ2Cover.RC 9 CertificateChecks.KernelJ2Cover.abGens
  CertificateChecks.KernelJ2Cover.invReps

#lc_reps CertificateChecks.KernelJ2Cover.RV 9 CertificateChecks.KernelJ2Cover.abGens
  CertificateChecks.KernelJ2Cover.uReps

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Child3

@[expose] noncomputable def fRC (j : Nat) : Bool :=
  repK 315 9 RC.GP RC.GIP 2 RC.CS RC.OFF RC.CI RC.E RC.P RC.L RC.K RC.S RC.SI RC.N 4000 j

@[expose] noncomputable def fRV (j : Nat) : Bool :=
  repK 315 9 RV.GP RV.GIP 2 RV.CS RV.OFF RV.CI RV.E RV.P RV.L RV.K RV.S RV.SI RV.N 4000 j

#lc_blocks RCBJ2 fRC 2835 16

#lc_blocks RVB fRV 1800 16

end CertificateChecks.KernelJ2Cover

end
