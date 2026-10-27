module

public import Certificates.Kernel.M3BSyl.SylData

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BS

open CFSG.KD.M3BS

theorem m3bs_let : letChk = true := by decide +kernel

theorem m3bs_gen : genChk gp gi gs = true := by decide +kernel

theorem m3bs_t : tChk tp tk = true := by decide +kernel

theorem m3bs_tw : tp.map CFSG.KC.M3BF.slpWT = Timmesfeld.M3B.sigW.toList := by rfl

theorem m3bs_pc : pcChk gs pc = true := by decide +kernel

theorem m3bs_u : uChk v us gs = true := by decide +kernel

end CFSG.KC.M3BS

end
