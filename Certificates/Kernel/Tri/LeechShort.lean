module

public import Certificates.Kernel.MonsterB.Short3014Orbit
public import CFSG.Monster.Tri.LeechCheckInputs

public section

namespace CertificateChecks.KernelLeech

open CFSG.Monster.Tri.Leech CertificateChecks.Short3014

theorem shortHit_eq (u : ℕ) : shortHit shortKlev u = memS u := by
  refine Bool.eq_iff_iff.2 ⟨fun h => ?_, fun h => ?_⟩
  ·
    rw [shortKlev, tablesKlev] at h
    unfold shortHit at h
    rw [Bool.and_eq_true, bne_iff_ne] at h
    exact (memS_iff u).2 ((klev_iff u).1 h.2)
  · have hr := (memS_iff u).1 h
    rw [shortKlev, tablesKlev]
    unfold shortHit
    rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_iff]
    exact ⟨(reach_short hr).1, (klev_iff u).2 hr⟩

theorem shortHit_fun : shortHit shortKlev = memS := funext shortHit_eq

end CertificateChecks.KernelLeech

end
