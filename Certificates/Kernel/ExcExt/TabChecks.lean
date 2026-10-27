module

public import Certificates.Data.Kernel.ExcExt.TabCheck
public import Certificates.Data.CFSGNative.ExcCensus.Tables
public import Certificates.Kernel.ExcExt.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame.ExcRaw

set_option maxRecDepth 100000

theorem ch712526tab0 : tabBool 0 (dim 0) (nroots 0) D.T0 (tabF 0) (tabH 0) (tabF 0) (tabH 0)
    (dim 0) D.fx0 D.hx0 D.fx0 D.hx0 tabFix1 = true := by quickRfl

theorem ch712526tab1 : tabBool 1 (dim 1) (nroots 1) D.T1 (tabF 1) (tabH 1) (tabF 1) (tabH 1)
    (dim 1) D.fx1 D.hx1 D.fx1 D.hx1 tabFix1 = true := by quickRfl

theorem ch712526tab2 : tabBool 2 (dim 2) (nroots 2) D.T2 (tabF 2) (tabH 2) (tabF 2) (tabH 2)
    (dim 2) D.fx2 D.hx2 D.fx2 D.hx2 tabFix1 = true := by quickRfl

theorem ch712526tab3 : tabBool 3 (dim 3) (nroots 3) D.T3 (tabF 3) (tabH 3) (tabF 2) (tabH 2)
    (dim 2) D.fx3 D.hx3 D.fx2 D.hx2 tabFix1 = true := by quickRfl

theorem ch712526tab4 : tabBool 4 (dim 4) (nroots 4) D.T4 (tabF 4) (tabH 4) (tabF 4) (tabH 4)
    (dim 4) D.fx4 D.hx4 D.fx4 D.hx4 tabFix1 = true := by quickRfl

theorem ch712526zm0 : zmRangeOK D.T0 0 81 = true := by quickRfl

theorem ch712526zm1 : zmRangeOK D.T1 0 81 = true := by quickRfl

theorem ch712526zm2 : zmRangeOK D.T2 0 729 = true := by quickRfl

theorem ch712526zm3 : zmRangeOK D.T3 0 243 = true := by quickRfl

theorem ch712526zm4 : zmRangeOK D.T4 0 2187 = true := by quickRfl

end CFSG.ExcExtK

end
