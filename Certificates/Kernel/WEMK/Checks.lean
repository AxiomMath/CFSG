module

public import Certificates.Kernel.WEMK.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option Elab.async false

public section

namespace CFSG.KD.WEMK

open Certificates.ExcModel Certificates.WEMK

theorem n4_ok : (kCore 4 N4.S N4.V N4.tab N4.par N4.wd N4.x0 N4.t0 N4.tr N4.ord &&
    kCovN 4 N4.S ((n4S ()).map toN) N4.V N4.cov) = true := by
  decide +kernel

theorem en4_ok : (kCore 4 EN4.S EN4.V EN4.tab EN4.par EN4.wd EN4.x0 EN4.t0 EN4.tr EN4.ord &&
    kCovN 4 EN4.S ((en4S ()).map toN) EN4.V EN4.cov) = true := by
  decide +kernel

theorem k5_ok : (kCore 6 K5.S K5.V K5.tab K5.par K5.wd K5.x0 K5.t0 K5.tr K5.ord &&
    kCovK 6 K5.S (ct5N ()) K5.V K5.cov [20, 9, 25, 41, 3]) = true := by
  decide +kernel

theorem k6_ok : (kCore 6 K6.S K6.V K6.tab K6.par K6.wd K6.x0 K6.t0 K6.tr K6.ord &&
    kCovK 6 K6.S (ct6N ()) K6.V K6.cov [41, 121, 19, 50, 83, 6]) = true := by
  decide +kernel

end CFSG.KD.WEMK

end
