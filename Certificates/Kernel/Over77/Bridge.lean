module

public import Certificates.Kernel.Over77.Data
public import Certificates.Data.Kernel.Over77.Bridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77Data

public section

namespace CFSG.KD.Over77

open CFSG.KC.Over77 CFSG.KC.Enum
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77 (dataA dataB dataZ dataSigma dataS idA)

theorem c12630bridge : (bridgeK A dataA && bridgeK B dataB && bridgeK Z dataZ &&
    bridgeK Sig dataSigma && allN 9 (fun k => bridgeK (nth S k) (dataS.getD k idA))) = true := by
  decide +kernel

theorem c12630bridgeNeg : (!bridgeK A dataB) = true := by decide +kernel

end CFSG.KD.Over77

end
