module

public import Certificates.Kernel.HN1408.ShIIData
public import Certificates.Kernel.HN1408.ShIIDefs
public import Certificates.Kernel.HN1408.TableIChk
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIICheck
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CayleyDefs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog

theorem shkHY3 : cyHd y3Words 480 capS ShIIY3.G ShIIY3.GI ShIIY3I ShIIY3.T ShIIY3.PL ShIIY3.cnt =
    true := by quickRfl
theorem shkHN3 : cyHd n3Words 240 capS ShIIN3.G ShIIN3.GI ShIIN3I ShIIN3.T ShIIN3.PL ShIIN3.cnt =
    true := by quickRfl
theorem shkHV3 : cyHd v3Words 4 capS ShIIV3.G ShIIV3.GI ShIIV3I ShIIV3.T ShIIV3.PL ShIIV3.cnt =
    true := by quickRfl
theorem shkHA3 : cyHd a3Words 60 capS ShIIA3.G ShIIA3.GI ShIIA3I ShIIA3.T ShIIA3.PL ShIIA3.cnt =
    true := by quickRfl

theorem shkRY3 : cyRec y3Words.length ShIIY3.G ShIIY3.GI ShIIY3I ShIIY3.T ShIIY3.PL ShIIY3.POS
    ShIIY3.SRT ShIIY3.SRI ShIIY3.HS ShIIY3.HSI ShIIY3Cl ShIIY3.cnt = true := by quickRfl
theorem shkRN3 : cyRec n3Words.length ShIIN3.G ShIIN3.GI ShIIN3I ShIIN3.T ShIIN3.PL ShIIN3.POS
    ShIIN3.SRT ShIIN3.SRI ShIIN3.HS ShIIN3.HSI ShIIN3Cl ShIIN3.cnt = true := by quickRfl
theorem shkRV3 : cyRec v3Words.length ShIIV3.G ShIIV3.GI ShIIV3I ShIIV3.T ShIIV3.PL ShIIV3.POS
    ShIIV3.SRT ShIIV3.SRI ShIIV3.HS ShIIV3.HSI ShIIV3Cl ShIIV3.cnt = true := by quickRfl
theorem shkRA3 : cyRec a3Words.length ShIIA3.G ShIIA3.GI ShIIA3I ShIIA3.T ShIIA3.PL ShIIA3.POS
    ShIIA3.SRT ShIIA3.SRI ShIIA3.HS ShIIA3.HSI ShIIA3Cl ShIIA3.cnt = true := by quickRfl

theorem shk3 : sh3K (WK fix3.rep) ShIIY3.GI ShIIY3.T ShIIY3.cnt ShIIN3.GI ShIIN3.T ShIIN3.cnt
    ShIIV3.GI ShIIV3.T ShIIV3.cnt ShIIA3.GI ShIIA3.T ShIIA3.cnt ShIIPY3 ShIIPN3 = true := by
  quickRfl

theorem shkLA : bAnd(headL 5 labsA3 60 ShIILA.G ShIILA.GI ShIILAJ ShIILA.T ShIILA.PL ShIILA.cnt,
    shLRec 5 ShIILA.G ShIILA.GI ShIILAJ ShIILA.T ShIILA.PL ShIILA.POS ShIILA.SRT ShIILA.SRI ShIILA.HS
      ShIILA.HSI ShIILACl ShIILA.cnt) = true := by quickRfl

theorem shkBA : bindListK 1408 4 (ShIIB 0) (ShIIBA.chars.map fun c => c.toNat - 48) = true := by
  quickRfl

theorem shkDA : shBlkK (ShIIB 0) 5 a3Words ShIILA.GI = true := by quickRfl

end CFSG.KD.HN1408

end
