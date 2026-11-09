module

public import Certificates.Kernel.HeMult.TabQ
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

public section

#kss_each CFSG.KD.HeMult.RQ1 CFSG.KD.HeMult.famRQ1 12

namespace CFSG.KD.HeMult

theorem R1.all : ∀ i, i < nat_lit 3 → famR1 i = true := by
  intro i hi
  have hi3 : i < 3 := hi
  unfold famR1
  refine famR_of_quarters fun q hq => ?_
  have h := RQ1.all (4 * i + q) (by show 4 * i + q < 12; omega)
  unfold famRQ1 at h
  have e : Nat.add (4 * i + q) (nat_lit 12) = 4 * Nat.add i (nat_lit 3) + q := by
    show 4 * i + q + 12 = 4 * (i + 3) + q
    omega
  rwa [e] at h

end CFSG.KD.HeMult

end
