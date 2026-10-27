module

public import Certificates.Kernel.PropA.Data
public import Certificates.Kernel.PropA.PData
public import Certificates.Kernel.PropA.PWords
public import Certificates.Data.Kernel.Spor.PRec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PRec

theorem pa450010_PD_ok : bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 2
    pa450010wd (pa450010PD 0), permOK 28 5 (mask 5) (28 * 5) (pa450010PD 0) (pa450010PD 1)) =
    true := by quickRfl

theorem pa450010_CKG1_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 480
    pa450010CKG1.k pa450010CKG1.G pa450010CKG1.GI pa450010CKG1.cnt pa450010CKG1.T pa450010CKG1.PL
    4 pa450010S1 pa450010S1I pa450010wCKG = true := by quickRfl
theorem pa450010_CKG1_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010CKG1.G pa450010CKG1.GI
    pa450010CKG1.k pa450010CKG1.cnt pa450010CKG1.T pa450010CKG1.PL pa450010CKG1.POS
    pa450010CKG1.SRT pa450010CKG1.SRI 0 480 = true := by quickRfl
theorem pa450010_CKG1_cent : bAnd(centK 28 5 (mask 5) (28 * 5) pa450010CKG1.k pa450010CKG1.G
    (pa450010S1 2), centK 28 5 (mask 5) (28 * 5) pa450010CKG1.k pa450010CKG1.G
    (pcomp 28 5 (mask 5) (pcomp 28 5 (mask 5) (pa450010PD 0) pa450010XD.R) (pa450010PD 1))) =
    true := by quickRfl

theorem pa450010_CKG2_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 480
    pa450010CKG2.k pa450010CKG2.G pa450010CKG2.GI pa450010CKG2.cnt pa450010CKG2.T pa450010CKG2.PL
    4 pa450010S2 pa450010S2I pa450010wCKG = true := by quickRfl
theorem pa450010_CKG2_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010CKG2.G pa450010CKG2.GI
    pa450010CKG2.k pa450010CKG2.cnt pa450010CKG2.T pa450010CKG2.PL pa450010CKG2.POS
    pa450010CKG2.SRT pa450010CKG2.SRI 0 480 = true := by quickRfl
theorem pa450010_CKG2_cent : bAnd(centK 28 5 (mask 5) (28 * 5) pa450010CKG2.k pa450010CKG2.G
    (pa450010S2 2), centK 28 5 (mask 5) (28 * 5) pa450010CKG2.k pa450010CKG2.G
    (pcomp 28 5 (mask 5) (pcomp 28 5 (mask 5) (pa450010PD 0) pa450010XD.R) (pa450010PD 1))) =
    true := by quickRfl

end CertificateChecks.KernelPropA

end
