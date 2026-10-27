module

public import Certificates.Kernel.GammaU.Sylow1Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUY1

open CFSG.KC.IF4C CFSG.KC.GUY

theorem cs16973b_b0 : blk 0 0 = true := by decide +kernel

theorem cs16973b_b1 : blk 1 0 = true := by decide +kernel

theorem cs16973b_lvl : (lvl 0 && lvl 1) = true := by decide +kernel

theorem cs16973b_gens : gens = true := by decide +kernel

theorem cs16973b_sift :
    CFSG.KC.IF4R.recsOK CFSG.KD.GUS1.T CFSG.KD.GUS1.O 1 (fun _ => idP) TS QS = true := by
  decide +kernel

theorem cs16973b_conj : conjOK CFSG.KD.GUS1.SP CFSG.KD.GUS1.SI Y ZP DP 576 E = true := by
  decide +kernel

theorem cs16973b_ord : ordOK Y = true := by decide +kernel

theorem cs16973b_nc : ncP (look ASP 0) (look ASP 1) = true := by decide +kernel

theorem cs16973b_cent :
    centOK (CFSG.KC.IF4R.packR CFSG.GF2Type.Smith1979.GammaU.SigmaP.thetaRows)
      [look CFSG.KD.GUS1.SP 0, look CFSG.KD.GUS1.SP 1] = true := by
  decide +kernel

end CFSG.KD.GUY1

end
