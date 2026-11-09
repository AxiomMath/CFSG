module

public import Certificates.Kernel.HeMult.TabQ
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

public section

#kss_each CFSG.KD.HeMult.RQ0 CFSG.KD.HeMult.famRQ0 12

namespace CFSG.KD.HeMult

theorem R0.all : ∀ i, i < nat_lit 3 → famR0 i = true := by
  intro i hi
  have hi3 : i < 3 := hi
  unfold famR0
  refine famR_of_quarters fun q hq => ?_
  have h := RQ0.all (4 * i + q) (by show 4 * i + q < 12; omega)
  unfold famRQ0 at h
  exact h

end CFSG.KD.HeMult

end
