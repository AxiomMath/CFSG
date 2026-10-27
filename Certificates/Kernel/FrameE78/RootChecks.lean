module

public import Certificates.Kernel.FrameE78.Data
public import Certificates.Data.Kernel.FrameE78RootK
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.FrameE78

#kc_each CFSG.KD.FrameE78 ch709549r_
  (fun k => rtRep 7 63 RP7 V7 (getS b7 k) (getS (getLs Q7 k) 0) 0 1093) 0 5

theorem ch709549neg :
    bAnd(notB (strictB (vget V7 (getS b7 0)) fun x =>
      allN 1093 fun j => rtPlane 7 63 RP7 (rtMask 63 RP7) x (negL x) (getS (getLs Q7 0) 0)
        (vget V7 j)),
    bAnd(notB (strictB (vget V7 (getS b7 2)) fun x =>
      allN 1093 fun j => rtPlane 7 63 RP7 1 x (negL x) (getS (getLs Q7 2) 0) (vget V7 j)),
      notB (strictB (vget V7 (getS b7 2)) fun x =>
        orB (bitB (rtMask 63 RP7) (vget V7 4)) (orB (bitB (rtMask 63 RP7) (addV3 7 (vget V7 4) x))
          (bitB (rtMask 63 RP7) (addV3 7 (vget V7 4) (negL x))))))) = true := by quickRfl

end CFSG.KD.FrameE78

end
