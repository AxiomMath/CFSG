module

public import Certificates.Kernel.HN1408.R0KDefs
public import Certificates.Kernel.HN1408.R0KFData
public import Certificates.Kernel.HN1408.TableIData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.ACheck
public import Certificates.Kernel.HN1408.CayleyDefs
public import Certificates.Kernel.HN1408.CzTDefs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408.R0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel CFSG.KD.HN1408.CzT CFSG.KD.HN1408.AK

theorem ch441665sq : sqK TI1.T (WK wordZ) = true := by quickRfl

theorem ch441665norm : normK G TI1.GI TI1.T = true := by quickRfl

theorem ch441665inter : withU (fun X0 X1 X2 X3 X4 X5 => interK X0 X1 X2 X3 X4 X5 1 TI1.T) = true := by
  quickRfl

theorem ch441665eich : withU (fun X0 X1 X2 X3 X4 X5 => eichK X0 X1 X2 X3 X4 X5 1 TI1.T) = true := by
  quickRfl

theorem ch441665surj : withU (fun X0 X1 X2 X3 X4 X5 => surjK X0 X1 X2 X3 X4 X5 1 TI1.T) = true := by
  quickRfl

theorem ch441665faith : faithK T0 T1 TI1.GI (WK wordZ) 256 TI1.T = true := by quickRfl

theorem ch441665fz : commWK fWords (WK wordZ₁) = true := by quickRfl

theorem ch441665fHd : cyHd fWords 60 aCap R0KF.G R0KF.GI R0KFI R0KF.T R0KF.PL R0KF.cnt = true := by
  quickRfl

theorem ch441665fRec : cyRec fWords.length R0KF.G R0KF.GI R0KFI R0KF.T R0KF.PL R0KF.POS R0KF.SRT
    R0KF.SRI R0KF.HS R0KF.HSI R0KFCl R0KF.cnt = true := by
  quickRfl

theorem ch441665fCay : cayK a5Mul 2930 [1022, 2678] fWords.length R0KF.cnt R0KF.PL R0KFCl
    (cayCodes a5Mul 2930 [1022, 2678] R0KF.PL R0KF.cnt) = true := by
  quickRfl

end CFSG.KD.HN1408.R0K

end
