module

public import Certificates.Kernel.Sporadic.Fi24F4.WC
import CFSG.Certificates.Kernel.Common.SliceRange

public section

#kc_slice_range CFSG.KD.Fi24F4.cvA CFSG.KD.Fi24F4.Ck.cvA 3 4
#kc_slice_range CFSG.KD.Fi24F4.cvB CFSG.KD.Fi24F4.Ck.cvB 3 4

namespace CFSG.KD.Fi24F4.Ck

open CFSG.KC.Fi24F4W

theorem cov3 : cov (nat_lit 3) = true := by
  have h1 := cvA3
  have h2 := cvB3
  unfold cvA at h1
  unfold cvB at h2
  unfold cov coverOK
  rw [h1, h2] <;> rfl

end CFSG.KD.Fi24F4.Ck

end
