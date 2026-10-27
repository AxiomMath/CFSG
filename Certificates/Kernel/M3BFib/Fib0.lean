module

public import Certificates.Kernel.M3BFib.FibData
public import Certificates.Kernel.M3BFib.Fib0Data

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF

theorem m3bf_word0 : wordChk LpM lk g0 = true := by decide +kernel

theorem m3bf_gen0 : genChk LpM oneK g0 = true := by decide +kernel

theorem m3bf_coord0 : coordChk (mapsOf g0) sM sI kM = true := by decide +kernel

theorem m3bf_norm0 : normChk kM hw nw dT = true := by decide +kernel

theorem m3bf_tab0 : tabChk dT tb = true := by decide +kernel

theorem m3bf_root0 : rootChk sM dT r0 = true := by decide +kernel

theorem m3bf_mask0 : (maskChk r0 mk && mk.length == 9) = true := by decide +kernel

end CFSG.KC.M3BF

end
