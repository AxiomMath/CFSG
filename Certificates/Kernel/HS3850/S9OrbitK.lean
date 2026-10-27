module

public import Certificates.Kernel.HS3850.S9Orbit
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CFSG.KD.HS3850.S9

theorem kKeys : (((List.range 4125).all fun k => (setC k).all (· < 3850)) &&
    CFSG.Sporadic.Schreier.Native.strictlyIncreasing
      (CFSG.KC.EvenSporDS81.isortN ((List.range 4125).map fun k => setKeyC (setC k)))) = true := by
  decide +kernel

end CFSG.KD.HS3850.S9
