module

public import Certificates.Kernel.GammaU.Pair0Data
public import Certificates.Kernel.GammaU.Pair1Data
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairInputs
public import Certificates.Data.Kernel.GammaUSigmaK
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUP0 cp16966a CFSG.KD.GUP0.row 0 12
#kc_each CFSG.KD.GUP1 cp16966b CFSG.KD.GUP1.row 0 4

namespace CFSG.KD.GUP0

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.GF2Type.Smith1979.GammaU

#kc_forall_chunks cp16966a_all (fun x => row x = true) 12 CFSG.KD.GUP0.cp16966a 1

theorem cp16966a_pcj : allBelow 4 pcj = true := by decide +kernel

theorem cp16966a_dup : allBelow 12 dup = true := by decide +kernel

theorem cp16966a_lists : lists = true := by decide +kernel

theorem cp16966a_rc : RC = (ResPair.resConj 0).map CFSG.KC.IF4R.packR := by decide +kernel

theorem cp16966a_rcrows : ((ResPair.resConj 0).all fun r => CFSG.KC.GUS.rowsOK r.toList) = true := by
  decide +kernel

end CFSG.KD.GUP0

namespace CFSG.KD.GUP1

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.GF2Type.Smith1979.GammaU

#kc_forall_chunks cp16966b_all (fun x => row x = true) 4 CFSG.KD.GUP1.cp16966b 1

theorem cp16966b_pcj : allBelow 4 pcj = true := by decide +kernel

theorem cp16966b_dup : allBelow 4 dup = true := by decide +kernel

theorem cp16966b_lists : lists = true := by decide +kernel

theorem cp16966b_rc : RC = (ResPair.resConj 1).map CFSG.KC.IF4R.packR := by decide +kernel

theorem cp16966b_rcrows : ((ResPair.resConj 1).all fun r => CFSG.KC.GUS.rowsOK r.toList) = true := by
  decide +kernel

end CFSG.KD.GUP1

end
