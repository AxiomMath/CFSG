module

public import Certificates.Data.Kernel.ExcExt.TabCheck
public import Certificates.Data.CFSGNative.ExcCensus.Tables
public import Certificates.Kernel.ExcExt.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame.ExcRaw

set_option maxRecDepth 100000

theorem ch712526tab5 : tabBool 5 (dim 5) (nroots 5) D.T5 (tabF 5) (tabH 5) (tabF 5) (tabH 5)
    (dim 5) D.fx5 D.hx5 D.fx5 D.hx5 tabFix1 = true := by quickRfl

theorem ch712526zm5_0 : zmRangeOK D.T5 (729 * 0) 729 = true := by quickRfl
theorem ch712526zm5_1 : zmRangeOK D.T5 (729 * 1) 729 = true := by quickRfl
theorem ch712526zm5_2 : zmRangeOK D.T5 (729 * 2) 729 = true := by quickRfl
theorem ch712526zm5_3 : zmRangeOK D.T5 (729 * 3) 729 = true := by quickRfl
theorem ch712526zm5_4 : zmRangeOK D.T5 (729 * 4) 729 = true := by quickRfl
theorem ch712526zm5_5 : zmRangeOK D.T5 (729 * 5) 729 = true := by quickRfl
theorem ch712526zm5_6 : zmRangeOK D.T5 (729 * 6) 729 = true := by quickRfl
theorem ch712526zm5_7 : zmRangeOK D.T5 (729 * 7) 729 = true := by quickRfl
theorem ch712526zm5_8 : zmRangeOK D.T5 (729 * 8) 729 = true := by quickRfl

end CFSG.ExcExtK

end
