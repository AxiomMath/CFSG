module

public import Certificates.Kernel.Misc.GL4.EAK
public import CFSG.Certificates.Kernel.Misc.GL4LatSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelMisc.GL4EA

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4
open CFSG.KC.Misc.Clos (ExactList allR)
open Certificates.GL4 (GL4)

theorem eaAt_ok (k : ℕ) (hk : k < 20160) : eaAt k = true := by
  have h := GEAK.all (k / 5040) (Nat.lt_of_lt_of_le (by omega : k / 5040 < 4) (by decide))
  exact (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 h k (Nat.mul_div_le k 5040) (by
    change k < 5040 * (k / 5040) + 5040
    omega)

theorem ea_exact : ExactList enc4 ⊤ 20160 EA := by
  refine top_exact (fun k hk => exists_of_invW (andB_iff.1 (eaAt_ok k hk)).1) fun k hk => ?_
  have h := (andB_iff.1 (eaAt_ok k (by omega))).2
  exact Nat.blt_eq.mp (impB_iff.1 h (Nat.blt_eq.mpr hk))

end CertificateChecks.KernelMisc.GL4EA

end
