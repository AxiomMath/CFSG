module

public import Certificates.Kernel.GammaU.Census0Data
public import Certificates.Kernel.GammaU.Census1Data
public import Certificates.Kernel.GammaU.CensusCfgData
public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs
public import CFSG.GF2Type.Smith1979.GammaU.SpanList
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUCC

open CFSG.KC.IF4C CFSG.KC.GUC

@[expose] noncomputable def pairs0 (n : Nat) : Bool :=
  allBelow 108 fun j => pairOK (CFSG.GF2Type.Smith1979.GammaU.spanList
    CFSG.GF2Type.Smith1979.GammaU.StepA.d0) CFSG.KD.GUC0.S0 TE TEi DT DTi TB CFSG.KD.GUC0.FT
    CFSG.KD.GUC0.FC 384 IX n j

@[expose] noncomputable def pairs1 (n : Nat) : Bool :=
  allBelow 108 fun j => pairOK (CFSG.GF2Type.Smith1979.GammaU.spanList
    CFSG.GF2Type.Smith1979.GammaU.StepA.d0) CFSG.KD.GUC1.S0 TE TEi DT DTi TB CFSG.KD.GUC1.FT
    CFSG.KD.GUC1.FC 384 IX n j

end CFSG.KD.GUCC

#kc_each CFSG.KD.GUCC cc16966c_p0 (fun n => CFSG.KD.GUCC.pairs0 n) 0 4
#kc_each CFSG.KD.GUCC cc16966c_p1 (fun n => CFSG.KD.GUCC.pairs1 n) 0 4

namespace CFSG.KD.GUCC

open CFSG.KC.IF4C CFSG.KC.GUC

#kc_forall_chunks cc16966c_p0all (fun n => pairs0 n = true) 4 CFSG.KD.GUCC.cc16966c_p0 1
#kc_forall_chunks cc16966c_p1all (fun n => pairs1 n = true) 4 CFSG.KD.GUCC.cc16966c_p1 1

theorem cc16966c_tb : tbOK CFSG.KD.GUC0.CG TB = true := by decide +kernel

theorem cc16966c_inv : (invOK TE TEi NE && invOK DT DTi 108 && Nat.beq NE 4) = true := by
  decide +kernel

end CFSG.KD.GUCC

end
