module

public import Certificates.Data.Kernel.SmithL6Rank

public section

namespace CertificateChecks.KernelSmithL6Rank

open CFSG.SmithL6 CFSG.SmithL6.Kernel

theorem rank0 : rankWitK 0 = true := by decide +kernel

theorem rank1 : rankWitK 1 = true := by decide +kernel

theorem rank2 : rankWitK 2 = true := by decide +kernel

theorem rank3 : rankWitK 3 = true := by decide +kernel

theorem rank4 : rankWitK 4 = true := by decide +kernel

theorem rank5 : rankWitK 5 = true := by decide +kernel

theorem rankK : chkRankK = true := by
  have hl : (rankRows.toList.length == 6 && rankCols.toList.length == 6 &&
      rankInv.toList.length == 6) = true := by decide +kernel
  unfold chkRankK
  rw [hl, Bool.true_and, List.all_eq_true]
  intro r hr
  have hr6 : r < 6 := List.mem_range.mp hr
  match r, hr6 with
  | 0, _ => exact rank0
  | 1, _ => exact rank1
  | 2, _ => exact rank2
  | 3, _ => exact rank3
  | 4, _ => exact rank4
  | 5, _ => exact rank5

theorem spanK : chkSpanWK = true := by decide +kernel

end CertificateChecks.KernelSmithL6Rank
