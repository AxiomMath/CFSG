module

public import Certificates.Kernel.M3BFib.FibData

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF

theorem m3bf_word1 : wordChk LpM lk g1 = true := by decide +kernel

theorem m3bf_gen1 : genChk LpM t1 g1 = true := by decide +kernel

theorem m3bf_bas1 : basisChk (mapsOf g1) b1 f1 = true := by decide +kernel

theorem m3bf_for1 : forestChk (mapsOf g1) b1 f1 r1 o1 = true := by decide +kernel

end CFSG.KC.M3BF

end
