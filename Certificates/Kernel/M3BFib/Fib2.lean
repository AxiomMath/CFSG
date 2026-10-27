module

public import Certificates.Kernel.M3BFib.FibData

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF

theorem m3bf_word2 : wordChk LpM lk g2 = true := by decide +kernel

theorem m3bf_gen2 : genChk LpM t2 g2 = true := by decide +kernel

theorem m3bf_bas2 : basisChk (mapsOf g2) b2 f2 = true := by decide +kernel

theorem m3bf_for2 : forestChk (mapsOf g2) b2 f2 r2 o2 = true := by decide +kernel

end CFSG.KC.M3BF

end
