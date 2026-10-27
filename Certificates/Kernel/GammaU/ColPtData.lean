module

public import Certificates.Kernel.GammaU.CensusCfgData
public import Certificates.Kernel.GammaU.Census0Data
public import Certificates.Kernel.GammaU.Census1Data
public import Certificates.Data.Kernel.GammaUColK
public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUCP "Certificates/Kernel/GammaU/data/colpt.json.gz" 1191
  13898629516946796711 (R0 : List (List Nat)) (R1 : List (List Nat))

namespace CFSG.KD.GUCP

open CFSG.KC.IF4C CFSG.KC.GUV

@[expose] noncomputable def cp0 : Bool :=
  cpOK (CFSG.GF2Type.Smith1979.GammaU.spanList CFSG.GF2Type.Smith1979.GammaU.StepA.d0)
    CFSG.KD.GUC0.S0 CFSG.KD.GUCC.TE CFSG.KD.GUCC.NE R0

@[expose] noncomputable def cp1 : Bool :=
  cpOK (CFSG.GF2Type.Smith1979.GammaU.spanList CFSG.GF2Type.Smith1979.GammaU.StepA.d0)
    CFSG.KD.GUC1.S0 CFSG.KD.GUCC.TE CFSG.KD.GUCC.NE R1

end CFSG.KD.GUCP

end
