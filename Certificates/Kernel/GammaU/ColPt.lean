
module

public import Certificates.Kernel.GammaU.ColPtOK
public import CFSG.Certificates.Kernel.GammaUColSound

public section

namespace CFSG.KD.GUCP

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem colPts_s0_0 (e : Nat) : e ∈ colPts (rowsP CFSG.KD.GUC0.S0) ↔
    ∃ n < CFSG.KD.GUCC.NE, ap12 (look CFSG.KD.GUCC.TE n) 3072 = e :=
  colPts_iff ccp16966_0 e

theorem colPts_s0_1 (e : Nat) : e ∈ colPts (rowsP CFSG.KD.GUC1.S0) ↔
    ∃ n < CFSG.KD.GUCC.NE, ap12 (look CFSG.KD.GUCC.TE n) 3072 = e :=
  colPts_iff ccp16966_1 e

end CFSG.KD.GUCP

end
