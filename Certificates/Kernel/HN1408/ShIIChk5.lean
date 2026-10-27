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

theorem shkHN5 : cyHd n5Words 125 capS ShIIN5.G ShIIN5.GI ShIIN5I ShIIN5.T ShIIN5.PL ShIIN5.cnt =
    true := by quickRfl
theorem shkHS5 : cyHd s5Words 16 capS ShIIS5.G ShIIS5.GI ShIIS5I ShIIS5.T ShIIS5.PL ShIIS5.cnt =
    true := by quickRfl
theorem shkHB5 : cyHd b5Words 100 capS ShIIB5.G ShIIB5.GI ShIIB5I ShIIB5.T ShIIB5.PL ShIIB5.cnt =
    true := by quickRfl
theorem shkHY5 : cyHd y5Words 240 capS ShIIY5.G ShIIY5.GI ShIIY5I ShIIY5.T ShIIY5.PL ShIIY5.cnt =
    true := by quickRfl

theorem shkRN5 : cyRec n5Words.length ShIIN5.G ShIIN5.GI ShIIN5I ShIIN5.T ShIIN5.PL ShIIN5.POS
    ShIIN5.SRT ShIIN5.SRI ShIIN5.HS ShIIN5.HSI ShIIN5Cl ShIIN5.cnt = true := by quickRfl
theorem shkRS5 : cyRec s5Words.length ShIIS5.G ShIIS5.GI ShIIS5I ShIIS5.T ShIIS5.PL ShIIS5.POS
    ShIIS5.SRT ShIIS5.SRI ShIIS5.HS ShIIS5.HSI ShIIS5Cl ShIIS5.cnt = true := by quickRfl
theorem shkRB5 : cyRec b5Words.length ShIIB5.G ShIIB5.GI ShIIB5I ShIIB5.T ShIIB5.PL ShIIB5.POS
    ShIIB5.SRT ShIIB5.SRI ShIIB5.HS ShIIB5.HSI ShIIB5Cl ShIIB5.cnt = true := by quickRfl
theorem shkRY5 : cyRec y5Words.length ShIIY5.G ShIIY5.GI ShIIY5I ShIIY5.T ShIIY5.PL ShIIY5.POS
    ShIIY5.SRT ShIIY5.SRI ShIIY5.HS ShIIY5.HSI ShIIY5Cl ShIIY5.cnt = true := by quickRfl

theorem shkCS5 : cayK s5Mul 0 [8, 3, 5] s5Words.length ShIIS5.cnt ShIIS5.PL ShIIS5Cl
    (cayCodes s5Mul 0 [8, 3, 5] ShIIS5.PL ShIIS5.cnt) = true := by quickRfl
theorem shkCB5 : cayK b5Mul 0 [92, 89] b5Words.length ShIIB5.cnt ShIIB5.PL ShIIB5Cl
    (cayCodes b5Mul 0 [92, 89] ShIIB5.PL ShIIB5.cnt) = true := by quickRfl

theorem shk5A : sh5AK (WK fix5A.rep) ShIIN5.GI ShIIN5.T ShIIN5.cnt ShIIS5.GI
    (fun c => WK (fix5A.cent.getD c [])) ShIIC5I ShIIPN5 = true := by quickRfl

theorem shk5B : allN 2 (fun j => commP (ShIIB5.GI j) (WK fix5B.rep)) = true := by quickRfl

theorem shk5C : sh5CK (WK fix5C.rep) ShIIY5.GI ShIIY5.T ShIIY5.cnt ShIIPY5 (WK wordA) (WK u5Word)
    (WK v5Word) (ShIIUVI 0) (ShIIUVI 1) (ShIIB 1) = true := by quickRfl

theorem shk7 : sh7K (WK fix7.rep) (WK w7Word) (WK wordA) (fun j => WK (fix7.cent.getD j [])) =
    true := by quickRfl

theorem shkLY : bAnd(headL 5 labsY5 120 ShIILY.G ShIILY.GI ShIILYJ ShIILY.T ShIILY.PL ShIILY.cnt,
    shLRec 5 ShIILY.G ShIILY.GI ShIILYJ ShIILY.T ShIILY.PL ShIILY.POS ShIILY.SRT ShIILY.SRI ShIILY.HS
      ShIILY.HSI ShIILYCl ShIILY.cnt) = true := by quickRfl

theorem shkBY : bindListK 1408 4 (ShIIB 1) (ShIIBY.chars.map fun c => c.toNat - 48) = true := by
  quickRfl

theorem shkDY : shBlkK (ShIIB 1) 5 y5Words ShIILY.GI = true := by quickRfl

end CFSG.KD.HN1408

end
