module

public import Certificates.Kernel.Sporadic.Fi24F4.WC
import CFSG.Certificates.Kernel.Common.SliceRange

public section

#kc_slice_range CFSG.KD.Fi24F4.cvA CFSG.KD.Fi24F4.Ck.cvA 0 1
#kc_slice_range CFSG.KD.Fi24F4.cvB CFSG.KD.Fi24F4.Ck.cvB 0 1

namespace CFSG.KD.Fi24F4.Ck

open CFSG.KC.Fi24F4W

theorem cov0 : cov (nat_lit 0) = true := by
  have h1 := cvA0
  have h2 := cvB0
  unfold cvA at h1
  unfold cvB at h2
  unfold cov coverOK
  rw [h1, h2] <;> rfl

end CFSG.KD.Fi24F4.Ck

end
