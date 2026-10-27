module

public import Certificates.Kernel.HS100.PairData
public import Certificates.Kernel.HS100.Five
public import CFSG.Certificates.Kernel.PairFreeSound

public section

namespace CertificateChecks.KernelHS100

open CFSG.RankThree.Native CFSG.RankThree.PartOne.K133Spor CFSG.KC.PairFree

theorem hsPairFree : HSPairFreeCheck := by
  unfold HSPairFreeCheck hsPairFreeOK
  rw [c0_pts, c2_pts, c23_pts, fiveLine_eq (j := 0) (by norm_num),
    fiveLine_eq (j := 2) (by norm_num), fiveLine_eq (j := 23) (by norm_num), pairFreeK_sound hw c0_pp (ppF (by norm_num)) pair0,
    pairFreeK_sound hw c2_pp (ppF (by norm_num)) pair2,
    pairFreeK_sound hw c23_pp (ppF (by norm_num)) pair23]
  rfl

end CertificateChecks.KernelHS100

end
