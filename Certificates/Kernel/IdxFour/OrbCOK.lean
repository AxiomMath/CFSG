module

public import Certificates.Kernel.IdxFour.OrbCData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4V

open CFSG.KC.IF4V

theorem cf17640t0 : orbCi G D L 0 = true := by decide +kernel

theorem cf17640t1 : orbCi G D L 1 = true := by decide +kernel

theorem cf17640t2 : orbCi G D L 2 = true := by decide +kernel

theorem cf17640t3 : orbCi G D L 3 = true := by decide +kernel

theorem cf17640ok : orbCOK G D L = true := by
  change (orbCi G D L 3 && (orbCi G D L 2 && (orbCi G D L 1 && (orbCi G D L 0 && true)))) = true
  rw [cf17640t0, cf17640t1, cf17640t2, cf17640t3]
  rfl

end CFSG.KD.IF4V

end
