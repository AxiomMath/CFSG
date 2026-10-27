
module

public import Certificates.Kernel.ONanNormal.Checks
public import Certificates.Kernel.ONanB2.Glue
public import CFSG.Certificates.Kernel.ONanNormalKSound

public section

namespace CertificateChecks.ONanNormal

open CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.NK

theorem normal2 : ∀ S : Subgroup CModel, IsPGroup 2 S → S.Normal → Nat.card S ≤ 4 :=
  normal2_CModel_of CertificateChecks.ONanB2.b2_hyp.bound CertificateChecks.ONanB2.b2_hyp.model
    fun S hSM hS2 hSn =>
      normal2_of CertificateChecks.ONanB2.b2_hyp ck6146_shape ck6146_chunks S hSM hS2 hSn

end CertificateChecks.ONanNormal
