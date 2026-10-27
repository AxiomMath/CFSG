module

public import Certificates.Kernel.PropA.Data
public import Certificates.Kernel.PropA.FactData
public import Certificates.Kernel.PropA.YData
public import Certificates.Kernel.PropA.FactWords
public import Certificates.Kernel.PropA.YWords
public import Certificates.Data.Kernel.Spor.PRec
public import Certificates.Data.Kernel.Spor.PMem
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PRec CFSG.KS.PMem

theorem pa450010_XR_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 2 pa450010XR.k
    pa450010XR.G pa450010XR.GI pa450010XR.cnt pa450010XR.T pa450010XR.PL 2 pa450010S1 pa450010S1I
    pa450010wXR = true := by quickRfl
theorem pa450010_XR_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010XR.G pa450010XR.GI
    pa450010XR.k pa450010XR.cnt pa450010XR.T pa450010XR.PL pa450010XR.POS pa450010XR.SRT
    pa450010XR.SRI 0 2 = true := by quickRfl
theorem pa450010_TX1_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 4 pa450010TX1.k
    pa450010TX1.G pa450010TX1.GI pa450010TX1.cnt pa450010TX1.T pa450010TX1.PL 4 pa450010S1
    pa450010S1I pa450010wTX = true := by quickRfl
theorem pa450010_TX1_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010TX1.G pa450010TX1.GI
    pa450010TX1.k pa450010TX1.cnt pa450010TX1.T pa450010TX1.PL pa450010TX1.POS pa450010TX1.SRT
    pa450010TX1.SRI 0 4 = true := by quickRfl
theorem pa450010_TX2_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 4 pa450010TX2.k
    pa450010TX2.G pa450010TX2.GI pa450010TX2.cnt pa450010TX2.T pa450010TX2.PL 4 pa450010S2
    pa450010S2I pa450010wTX = true := by quickRfl
theorem pa450010_TX2_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010TX2.G pa450010TX2.GI
    pa450010TX2.k pa450010TX2.cnt pa450010TX2.T pa450010TX2.PL pa450010TX2.POS pa450010TX2.SRT
    pa450010TX2.SRI 0 4 = true := by quickRfl

theorem pa450010_U_inJ : atK pa450010J.cnt pa450010J.T pa450010PU 0 pa450010UD.R = true := by
  quickRfl
theorem pa450010_CDU_filt : filtInK 28 5 (mask 5) pa450010CDU.cnt pa450010CDU.T 2 pa450010J.G
    pa450010XR.cnt pa450010XR.T pa450010PXU = true := by quickRfl

theorem pa450010_Y1_comm : allN 3 (fun j => centK 28 5 (mask 5) (28 * 5) pa450010Y1.k pa450010Y1.G
    (pa450010Y1.G j)) = true := by quickRfl
theorem pa450010_Y2_comm : allN 3 (fun j => centK 28 5 (mask 5) (28 * 5) pa450010Y2.k pa450010Y2.G
    (pa450010Y2.G j)) = true := by quickRfl
theorem pa450010_Y1_exp : bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) pa450010Y1.G pa450010Y1.GI 3
    [1, 1, 1, 1] (pidn 28 5), bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) pa450010Y1.G pa450010Y1.GI 3
    [2, 2, 2, 2] (pidn 28 5), wordEqK 28 5 (mask 5) (pidn 28 5) pa450010Y1.G pa450010Y1.GI 3
    [3, 3, 3, 3] (pidn 28 5))) = true := by quickRfl
theorem pa450010_Y2_exp : bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) pa450010Y2.G pa450010Y2.GI 3
    [1, 1, 1, 1] (pidn 28 5), bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) pa450010Y2.G pa450010Y2.GI 3
    [2, 2, 2, 2] (pidn 28 5), wordEqK 28 5 (mask 5) (pidn 28 5) pa450010Y2.G pa450010Y2.GI 3
    [3, 3, 3, 3] (pidn 28 5))) = true := by quickRfl

theorem pa450010_Z1_filt : filtInK 28 5 (mask 5) pa450010Y1.cnt pa450010Y1.T 5 pa450010CKX1.G
    pa450010TX1.cnt pa450010TX1.T pa450010PZ1 = true := by quickRfl
theorem pa450010_Z2_filt : filtInK 28 5 (mask 5) pa450010Y2.cnt pa450010Y2.T 5 pa450010CKX2.G
    pa450010TX2.cnt pa450010TX2.T pa450010PZ2 = true := by quickRfl

end CertificateChecks.KernelPropA
