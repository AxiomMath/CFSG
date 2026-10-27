module

public import Certificates.Data.Kernel.E7Plane.Check
public import Certificates.Kernel.E7Plane.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.E7Plane

open CFSG.KC.E7Plane

theorem sylK_two : sylK RV TB 2 1024 I2 W2 R2 = true := by quickRfl

theorem sylK_three : sylK RV TB 3 81 I3 W3 R3 = true := by quickRfl

theorem sylK_five : sylK RV TB 5 5 I5 W5 R5 = true := by quickRfl

theorem sylK_seven : sylK RV TB 7 7 I7 W7 R7 = true := by quickRfl

end CFSG.KD.E7Plane

end
