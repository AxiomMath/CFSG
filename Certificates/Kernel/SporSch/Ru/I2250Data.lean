module

public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Sporadic.Schreier.RuCheckInvInputs
meta import CFSG.Sporadic.Schreier.RuWitArrays
meta import CFSG.Sporadic.Schreier.RuCheckInvInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelSporSch.RuI

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def xM : Array (Array Nat) := #[ruFusXA 1, ruFusXA 2, ruFusXA 3]

meta def q1M : Array (Array Nat) := #[1, 2, 3].map fun i => compA 4060 (ruFusGA i) ruA0A

meta def q2M : Array (Array Nat) := #[1, 2, 3].map fun i =>
  compA 4060 (compA 4060 (ruFusGA i) ruA0A) (ruInv (ruFusGA i))

meta def q3M : Array (Array Nat) := #[1, 2, 3].map fun i =>
  compA 4060 (compA 4060 (compA 4060 (ruFusGA i) ruA0A) (ruInv (ruFusGA i))) (ruFusXA i)

meta def q4M : Array (Array Nat) := #[1, 2, 3].map fun i =>
  powA 4060 (compA 4060 (compA 4060 (compA 4060 (ruFusGA i) ruA0A) (ruInv (ruFusGA i)))
    (ruFusXA i)) ((ruFusD i - 1) / 2)

meta def hM : Array (Array Nat) := #[ruFusHA 1, ruFusHA 2, ruFusHA 3]

meta def haM : Array (Array Nat) := hM.map fun h => compA 4060 h ruA0A

meta def p01M : Array Nat := compA 4060 ruA0A ruA1A

meta def p10M : Array Nat := compA 4060 ruA1A ruA0A

meta def r2M : Array Nat := powA 4060 ruA1A 2

meta def r7M : Array Nat := powA 4060 ruAB2A 7

meta def r2bM : Array Nat := powA 4060 ruAB2A 2

meta def p010M : Array Nat := compA 4060 (compA 4060 ruA0A ruA1A) ruA0A

meta def q29M : Array Nat := compA 4060 (compA 4060 (compA 4060 ruA0A ruA1A) ruA0A) (powA 4060 ruA1A 2)

end CertificateChecks.KernelSporSch.RuI

#kss_perms CertificateChecks.KernelSporSch.RuI.X 12 CertificateChecks.KernelSporSch.RuI.xM
#kss_perms CertificateChecks.KernelSporSch.RuI.Q1 12 CertificateChecks.KernelSporSch.RuI.q1M
#kss_perms CertificateChecks.KernelSporSch.RuI.Q2 12 CertificateChecks.KernelSporSch.RuI.q2M
#kss_perms CertificateChecks.KernelSporSch.RuI.Q3 12 CertificateChecks.KernelSporSch.RuI.q3M
#kss_perms CertificateChecks.KernelSporSch.RuI.Q4 12 CertificateChecks.KernelSporSch.RuI.q4M
#kss_perms CertificateChecks.KernelSporSch.RuI.H 12 CertificateChecks.KernelSporSch.RuI.hM
#kss_perms CertificateChecks.KernelSporSch.RuI.HA 12 CertificateChecks.KernelSporSch.RuI.haM
#ks_perm CertificateChecks.KernelSporSch.RuI.P01 12 CertificateChecks.KernelSporSch.RuI.p01M
#ks_perm CertificateChecks.KernelSporSch.RuI.P10 12 CertificateChecks.KernelSporSch.RuI.p10M
#ks_perm CertificateChecks.KernelSporSch.RuI.R2 12 CertificateChecks.KernelSporSch.RuI.r2M
#ks_perm CertificateChecks.KernelSporSch.RuI.AB2 12 CFSG.Sporadic.RuSchreier.ruAB2A
#ks_perm CertificateChecks.KernelSporSch.RuI.R7 12 CertificateChecks.KernelSporSch.RuI.r7M
#ks_perm CertificateChecks.KernelSporSch.RuI.R2B 12 CertificateChecks.KernelSporSch.RuI.r2bM
#ks_perm CertificateChecks.KernelSporSch.RuI.P010 12 CertificateChecks.KernelSporSch.RuI.p010M
#ks_perm CertificateChecks.KernelSporSch.RuI.Q29 12 CertificateChecks.KernelSporSch.RuI.q29M

end
