module

public import Certificates.Kernel.M3BFib.FibData

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF

theorem m3bf_word3 : wordChk LpM lk g3 = true := by decide +kernel

theorem m3bf_gen3 : genChk LpM t3 g3 = true := by decide +kernel

theorem m3bf_bas3 : basisChk (mapsOf g3) b3 f3 = true := by decide +kernel

theorem m3bf_for3 : forestChk (mapsOf g3) b3 f3 r3 o3 = true := by decide +kernel

end CFSG.KC.M3BF

end
