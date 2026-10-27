module

public import Certificates.Kernel.PropA.Data
public import Certificates.Kernel.PropA.Words
public import Certificates.Data.Kernel.Spor.PRec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PRec

theorem pa450010_J_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 60 pa450010J.k
    pa450010J.G pa450010J.GI pa450010J.cnt pa450010J.T pa450010J.PL 2 pa450010S1 pa450010S1I
    pa450010wJ = true := by quickRfl
theorem pa450010_J_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010J.G pa450010J.GI
    pa450010J.k pa450010J.cnt pa450010J.T pa450010J.PL pa450010J.POS pa450010J.SRT pa450010J.SRI 0
    60 = true := by quickRfl
theorem pa450010_J_cent :
    centK 28 5 (mask 5) (28 * 5) pa450010J.k pa450010J.G pa450010XD.R = true := by quickRfl

theorem pa450010_CDX_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 240
    pa450010CDX.k pa450010CDX.G pa450010CDX.GI pa450010CDX.cnt pa450010CDX.T pa450010CDX.PL 2
    pa450010S1 pa450010S1I pa450010wCDX = true := by quickRfl
theorem pa450010_CDX_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010CDX.G pa450010CDX.GI
    pa450010CDX.k pa450010CDX.cnt pa450010CDX.T pa450010CDX.PL pa450010CDX.POS pa450010CDX.SRT
    pa450010CDX.SRI 0 240 = true := by quickRfl
theorem pa450010_CDX_cent :
    centK 28 5 (mask 5) (28 * 5) pa450010CDX.k pa450010CDX.G pa450010XD.R = true := by quickRfl

theorem pa450010_CDU_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 36
    pa450010CDU.k pa450010CDU.G pa450010CDU.GI pa450010CDU.cnt pa450010CDU.T pa450010CDU.PL 2
    pa450010S1 pa450010S1I pa450010wCDU = true := by quickRfl
theorem pa450010_CDU_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010CDU.G pa450010CDU.GI
    pa450010CDU.k pa450010CDU.cnt pa450010CDU.T pa450010CDU.PL pa450010CDU.POS pa450010CDU.SRT
    pa450010CDU.SRI 0 36 = true := by quickRfl
theorem pa450010_CDU_cent :
    centK 28 5 (mask 5) (28 * 5) pa450010CDU.k pa450010CDU.G pa450010UD.R = true := by quickRfl

theorem pa450010_CKX1_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 960
    pa450010CKX1.k pa450010CKX1.G pa450010CKX1.GI pa450010CKX1.cnt pa450010CKX1.T pa450010CKX1.PL
    4 pa450010S1 pa450010S1I pa450010wCKX = true := by quickRfl
theorem pa450010_CKX1_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010CKX1.G pa450010CKX1.GI
    pa450010CKX1.k pa450010CKX1.cnt pa450010CKX1.T pa450010CKX1.PL pa450010CKX1.POS
    pa450010CKX1.SRT pa450010CKX1.SRI 0 960 = true := by quickRfl
theorem pa450010_CKX1_cent :
    centK 28 5 (mask 5) (28 * 5) pa450010CKX1.k pa450010CKX1.G pa450010XD.R = true := by quickRfl

theorem pa450010_CKX2_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 960
    pa450010CKX2.k pa450010CKX2.G pa450010CKX2.GI pa450010CKX2.cnt pa450010CKX2.T pa450010CKX2.PL
    4 pa450010S2 pa450010S2I pa450010wCKX = true := by quickRfl
theorem pa450010_CKX2_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010CKX2.G pa450010CKX2.GI
    pa450010CKX2.k pa450010CKX2.cnt pa450010CKX2.T pa450010CKX2.PL pa450010CKX2.POS
    pa450010CKX2.SRT pa450010CKX2.SRI 0 960 = true := by quickRfl
theorem pa450010_CKX2_cent :
    centK 28 5 (mask 5) (28 * 5) pa450010CKX2.k pa450010CKX2.G pa450010XD.R = true := by quickRfl

theorem pa450010_R_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 60 pa450010R.k
    pa450010R.G pa450010R.GI pa450010R.cnt pa450010R.T pa450010R.PL 4 pa450010S1 pa450010S1I
    pa450010wR = true := by quickRfl
theorem pa450010_R_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010R.G pa450010R.GI
    pa450010R.k pa450010R.cnt pa450010R.T pa450010R.PL pa450010R.POS pa450010R.SRT pa450010R.SRI 0
    60 = true := by quickRfl
theorem pa450010_R_cent :
    centK 28 5 (mask 5) (28 * 5) pa450010R.k pa450010R.G pa450010C14.R = true := by quickRfl
end CertificateChecks.KernelPropA

end
