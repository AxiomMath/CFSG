module

public import Certificates.Data.CoreE1Mathieu
import all Init.Data.Range.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12E1

open Certificates.CoreE1Perm

theorem k_gens : gensOK m12E1Data = true := by decide +kernel

theorem k_e0 : entryOK m12E1Data 0 (m12E1Data.es.getD 0 default) = true := by decide +kernel

theorem k_e1 : entryOK m12E1Data 1 (m12E1Data.es.getD 1 default) = true := by decide +kernel

theorem k_e2 : entryOK m12E1Data 2 (m12E1Data.es.getD 2 default) = true := by decide +kernel

theorem k_e3 : entryOK m12E1Data 3 (m12E1Data.es.getD 3 default) = true := by decide +kernel

theorem k_len : (m12E1Data.es.length == m12E1Data.xWs.length) = true := by decide +kernel

end CertificateChecks.KernelLC.M12E1

end
