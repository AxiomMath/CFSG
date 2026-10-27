module

public import Certificates.Data.Kernel.L5.Sh2E16
import CFSG.Certificates.Kernel.Common.Each

public section

namespace CFSG.KD.L5.E16

open CFSG.Certificates.Kernel.L5S

set_option maxRecDepth 100000

theorem tabsE16_true : tabsE16 = true := by decide +kernel

#kc_each CFSG.KD.L5.E16.ch5068 0 4

theorem mvT_neg : mvT (mulK 0) (invK 0) rK rK = false := by decide +kernel

theorem e2T_neg : e2T (mulK 1) r1K = false := by decide +kernel

theorem e1T_neg : e1T (fun _ _ => (0, false)) = false := by decide +kernel

end CFSG.KD.L5.E16

end
