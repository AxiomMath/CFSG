module

public import Certificates.Kernel.M3BFib.FibData
public import Certificates.Data.Kernel.M3BFib.FibRoot

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF

theorem m3bf_lam1 : lamChk g1 = true := by decide +kernel
theorem m3bf_lam2 : lamChk g2 = true := by decide +kernel
theorem m3bf_lam3 : lamChk g3 = true := by decide +kernel

theorem m3bf_root1 : rootVChk LpM t1 1 r1 = true := by decide +kernel
theorem m3bf_root2 : rootVChk LpM t2 2 r2 = true := by decide +kernel
theorem m3bf_root3 : rootVChk LpM t3 3 r3 = true := by decide +kernel

end CFSG.KC.M3BF

end
