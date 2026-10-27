module

public import Certificates.Kernel.GammaU.Sylow0Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUY0

open CFSG.KC.IF4C CFSG.KC.GUY

theorem cs16973a_b0 : blk 0 0 = true := by decide +kernel

theorem cs16973a_b1 : blk 1 0 = true := by decide +kernel

theorem cs16973a_lvl : (lvl 0 && lvl 1) = true := by decide +kernel

theorem cs16973a_gens : gens = true := by decide +kernel

theorem cs16973a_sift :
    CFSG.KC.IF4R.recsOK CFSG.KD.GUS0.T CFSG.KD.GUS0.O 1 (fun _ => idP) TS QS = true := by
  decide +kernel

theorem cs16973a_conj : conjOK CFSG.KD.GUS0.SP CFSG.KD.GUS0.SI Y ZP DP 576 E = true := by
  decide +kernel

theorem cs16973a_ord : ordOK Y = true := by decide +kernel

theorem cs16973a_nc : ncP (look ASP 0) (look ASP 1) = true := by decide +kernel

theorem cs16973a_cent :
    centOK (CFSG.KC.IF4R.packR CFSG.GF2Type.Smith1979.GammaU.SigmaP.thetaRows)
      [look CFSG.KD.GUS0.SP 0, look CFSG.KD.GUS0.SP 1] = true := by
  decide +kernel

end CFSG.KD.GUY0

end
