module

public import Certificates.Data.Kernel.ONanCMK

public section

namespace CertificateChecks.ONanCM

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.CMK

theorem ck6145_letters : lettersK = true := by decide +kernel

theorem ck6145_rels : relsK cmRelCodes = true := by decide +kernel

theorem ck6145_chain : chainK [] cmChain = true := by decide +kernel

theorem ck6145_prod : chainProd cmChain = 161280 := by decide +kernel

end CertificateChecks.ONanCM
