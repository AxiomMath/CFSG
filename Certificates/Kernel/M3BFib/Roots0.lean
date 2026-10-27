module

public import Certificates.Kernel.M3BFib.Fib0Data
public import Certificates.Data.Kernel.M3BFib.Fib0Root

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF

theorem m3bf_lam0 : lamChk g0 = true := by decide +kernel

theorem m3bf_hn0 : (hw.all (Nat.blt · 4) && nw.all (Nat.blt · 4)) = true := by decide +kernel

theorem m3bf_rootv0 : rootVChk0 r0 = true := by decide +kernel

end CFSG.KC.M3BF

end
