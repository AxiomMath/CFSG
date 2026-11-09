module

public import Certificates.Kernel.HeMult.TabQ
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

public section

#kss_each CFSG.KD.HeMult.RQ2 CFSG.KD.HeMult.famRQ2 12

namespace CFSG.KD.HeMult

theorem R2.all : ∀ i, i < nat_lit 3 → famR2 i = true := by
  intro i hi
  have hi3 : i < 3 := hi
  unfold famR2
  refine famR_of_quarters fun q hq => ?_
  have h := RQ2.all (4 * i + q) (by show 4 * i + q < 12; omega)
  unfold famRQ2 at h
  have e : Nat.add (4 * i + q) (nat_lit 24) = 4 * Nat.add i (nat_lit 6) + q := by
    show 4 * i + q + 24 = 4 * (i + 6) + q
    omega
  rwa [e] at h

end CFSG.KD.HeMult

end
