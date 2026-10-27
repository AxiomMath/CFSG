module

public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Data.SmithL6WData

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6

theorem chk_card : wmk.all (fun M => (List.range 64).countP (fun x => M.testBit x) == 8) = true := by
  decide +kernel

theorem chk_wData : wData.toList.all (· < 262144) = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
