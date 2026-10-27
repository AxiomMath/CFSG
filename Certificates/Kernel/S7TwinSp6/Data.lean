module

public import Certificates.Kernel.LocalComp.Sp6J.Data
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Data.S7TwinSp6
public meta import Certificates.Kernel.LocalComp.Sp6J.Data
public meta import Certificates.Data.S7TwinSp6
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS7Sp6

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelLC.Sp6J Certificates.S7TwinSp6

meta def SG : Array (Array Nat) := (sylWords.map (evalW 36 XG)).toArray

meta def SS : Array (Array Nat) := strongOf 36 SG sylDerive

meta def baseS : Array Nat := #[4, 2, 0, 1]

meta def RSL : List (Array Nat) := fourWords.map (evalW 36 SG)

end CertificateChecks.KernelS7Sp6

#ks_rawchain CertificateChecks.KernelS7Sp6.SQ 36 6 36 CertificateChecks.KernelS7Sp6.SS
  CertificateChecks.KernelS7Sp6.baseS 4 Certificates.S7TwinSp6.sylDerive

#kss_cntord CertificateChecks.KernelS7Sp6.NS CertificateChecks.KernelS7Sp6.SQ 36 6
  CertificateChecks.KernelS7Sp6.SS CertificateChecks.KernelS7Sp6.baseS
  CertificateChecks.KernelLC.Sp6J.One36 CertificateChecks.KernelLC.Sp6J.id36 4

#lc_reps CertificateChecks.KernelS7Sp6.RS 6 CertificateChecks.KernelS7Sp6.SG
  CertificateChecks.KernelS7Sp6.RSL

end
