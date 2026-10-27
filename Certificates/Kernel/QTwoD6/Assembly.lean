module

public import CFSG.Certificates.Kernel.QTwoD6.Cell
import Certificates.Kernel.QTwoD6.Cover
import Certificates.Kernel.QTwoD6.RowsAll

public section

namespace CFSG.KD.QTwoD6

open CFSG.StandardType.QTwoD6

theorem qTwoD6_linearCell : GGQ2D6LinearCell :=
  K.linearCell_of_checks qTwoD6_sigInv
    qTwoD6_cov0 l0_all (fun j h0 h1 => t0_all j h0 (by
      have h : 4 * surv0.length = 16 := rfl
      rw [h] at h1
      exact h1))
    qTwoD6_cov1 l1_all (fun j h0 h1 => t1_all j h0 (by
      have h : 4 * surv1.length = 12 := rfl
      rw [h] at h1
      exact h1))
    qTwoD6_cov2 l2_all (fun j h0 h1 => t2_all j h0 (by
      have h : 4 * surv2.length = 12 := rfl
      rw [h] at h1
      exact h1))
    qTwoD6_covT lT_all (fun j h0 h1 => tT_all j h0 (by
      have h : 4 * survT.length = 12 := rfl
      rw [h] at h1
      exact h1))

end CFSG.KD.QTwoD6

end
