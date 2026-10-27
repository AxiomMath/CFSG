module

public import Certificates.Kernel.Hall82K.DAData
public import Certificates.Kernel.Hall82K.EnumData
public import Certificates.Data.Kernel.Hall82K.Bridge
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Hall82A

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Hall82K CFSG.KD.Hall82E
open CFSG.ComponentClassification.AS81.HeTri

theorem ch840002tr : P.allN 64 (transAtK EL DTW) = true := by decide +kernel

theorem ch840002kiff : kIffK 4439643498 = true ∧ kIffK 34633937090 = true := by decide +kernel

theorem ch840002nv : P.allN 2160 (nvAtOK EM EL DNV) = true := by decide +kernel

theorem ch840002li : lgenMemK EM DLI 52077576321 61871938592 = true := by decide +kernel

theorem ch840002z : zetaK DZC = true := by decide +kernel

theorem ch840002zc : codeArrK DZC heZetaArr = true := by decide +kernel

end CFSG.KD.Hall82A
