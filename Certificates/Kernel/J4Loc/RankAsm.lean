module

public import Certificates.Kernel.J4Loc.RankChk
public import Certificates.Kernel.J4Q.MaskU
public import CFSG.Certificates.Kernel.J4Loc.RankSound

public section

namespace CertificateChecks.KernelJ4Loc

open CFSG.Sporadic.J4.QT CFSG.KD.J4Q CFSG.KS.J4Loc

theorem k4174_kinv : ∀ i < 4, compT (kInvTab i) (kTab i) = idT := by
  intro i hi
  rw [KernelJ4Q.kTab_eq hi, KernelJ4Q.kInvTab_eq hi]
  have h := List.all_eq_true.1 ch4174_kinv i (List.mem_range.2 hi)
  exact beq_iff_eq.1 h

theorem k4174_rank {t : List ℕ} (ht : t ∈ tabL) (hne : t ≠ idT) :
    16 ≤ ((Finset.range 2048).image fun c => actT t c ^^^ c).card :=
  rank_ge_of k4174_kinv ht hne

end CertificateChecks.KernelJ4Loc

end
