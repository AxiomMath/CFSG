module

public import Certificates.Data.Kernel.ExcExt.Orbit
public import Certificates.Kernel.ExcExt.Data
public import Certificates.Kernel.ExcExt.OrbitData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcExtK

set_option maxRecDepth 100000

theorem ch712526orb0 : orbRangeOK D.T0 O.B0 [0, 1, 5, 9] 0 81 = true := by quickRfl

theorem ch712526orb1 : orbRangeOK D.T1 O.B1 [0, 1, 5, 9] 0 81 = true := by quickRfl

theorem ch712526orb2 : orbRangeOK D.T2 O.B2 [0, 1, 2, 3, 4, 8, 13, 27] 0 729 = true := by quickRfl

theorem ch712526orb3 : orbRangeOK D.T3 O.B3 [0, 1, 4, 11] 0 243 = true := by quickRfl

theorem ch712526orb4_0 : orbRangeOK D.T4 O.B4 [0, 1, 4, 11, 14, 416] 0 729 = true := by quickRfl
theorem ch712526orb4_1 : orbRangeOK D.T4 O.B4 [0, 1, 4, 11, 14, 416] 729 729 = true := by quickRfl
theorem ch712526orb4_2 : orbRangeOK D.T4 O.B4 [0, 1, 4, 11, 14, 416] 1458 729 = true := by quickRfl

theorem ch712526orb5_0 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 0 729 = true := by quickRfl
theorem ch712526orb5_1 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 729 729 = true := by quickRfl
theorem ch712526orb5_2 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 1458 729 = true := by quickRfl
theorem ch712526orb5_3 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 2187 729 = true := by quickRfl
theorem ch712526orb5_4 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 2916 729 = true := by quickRfl
theorem ch712526orb5_5 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 3645 729 = true := by quickRfl
theorem ch712526orb5_6 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 4374 729 = true := by quickRfl
theorem ch712526orb5_7 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 5103 729 = true := by quickRfl
theorem ch712526orb5_8 : orbRangeOK D.T5 O.B5 [0, 1, 4, 11, 14] 5832 729 = true := by quickRfl

end CFSG.ExcExtK

end
