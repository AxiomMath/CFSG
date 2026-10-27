module

public import Certificates.Kernel.ONanCM.Checks
public import CFSG.Certificates.Kernel.ONanCMKSound

public section

namespace CertificateChecks.ONanCM

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.CMK

theorem cmModel_facts : cmLettersOK = true ∧ cmRelOK = true ∧
    chainOK cmLetters [] cmChain = true ∧ chainProd cmChain = 161280 :=
  ⟨cmLettersOK_of ck6145_letters, cmRelOK_of ck6145_letters ck6145_rels,
    chainOK_of ck6145_letters ck6145_chain, ck6145_prod⟩

end CertificateChecks.ONanCM
