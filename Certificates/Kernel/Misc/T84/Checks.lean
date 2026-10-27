module

public import Certificates.Data.Kernel.Misc.T84K
public import Certificates.Data.T84PCheck
import all Certificates.Data.T84PCheck

public section

namespace CertificateChecks.KernelMisc.T84

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.GL4 CFSG.KC.Misc.T84

theorem ch442349_p0 : chP0 = true := by decide +kernel

theorem ch442349_vf : chVF = true := by decide +kernel

theorem ch442349_j : chJ = true := by decide +kernel

theorem ch442349_cent : chCent = true := by decide +kernel

theorem ch442349_y : chY = true := by decide +kernel

theorem ch442349_rank : chRankOn IMK Certificates.T84PCheck.rankIdx = true := by decide +kernel

theorem ch442349_only : chOnly = true := by decide +kernel

theorem ch442349_d0 : ((List.range 4).flatMap fun i => (List.range 2).map fun j =>
    Certificates.Asc82NormA6.rhoCode (Certificates.T84P.g1 ^ i * Certificates.T84P.g2 ^ j)) = D0c := by
  decide +kernel

theorem ch442349_s0 : ((Finset.univ.filter fun a : Equiv.Perm (Fin 6) => a.sign = 1).image
    Certificates.Asc82NormA6.rhoCode) = S0L.toFinset := by
  decide +kernel

end CertificateChecks.KernelMisc.T84

end
