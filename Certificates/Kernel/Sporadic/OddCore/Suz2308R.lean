module

public import Certificates.Kernel.Sporadic.OddCore.Suz2308K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.S2308

open CFSG.KC.Enum CFSG.KS CFSG.KS.Row CFSG.KS.Raw CertificateChecks.KernelSpor

theorem fpermR : allN 14 (fun j => rpermK 22880 15 (mask 15) S2308FXI (ofs j) S2308FX (ofs j)) =
    true := by quickRfl

theorem crev : allN 12 (fun k => rpermK 22880 15 (mask 15) SuzCertI (ofs k) SuzCertT.F (ofs k)) =
    true := by quickRfl

theorem gpermR : rpermK 22880 15 (mask 15) S2308GXI 0 S2308GX 0 = true := by quickRfl

theorem lperm : allN 14 (fun j => permOK 280 9 (mask 9) (280 * 9) (S2308LC.S j) (S2308LC.SI j)) =
    true := by quickRfl

end CertificateChecks.KernelSpor.OddCore.S2308

end
