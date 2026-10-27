
module

public import Certificates.Kernel.ONanB2.Checks
public import Certificates.Kernel.ONanCM.Checks
public import CFSG.Certificates.Kernel.ONanB2KSound

public section

namespace CertificateChecks.ONanB2

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.B2K

theorem b2_hyp : Hyp :=
  ⟨CertificateChecks.ONanCM.ck6145_letters, cmBoundCheck_cert, cmModelCheck_cert, ck6149_base⟩

theorem b2_checks : Checks :=
  ⟨ck6149_fz, ck6149_r, ck6149_irred, ck6149_s, ck6149_t, ck6149_tcent, ck6149_y,
    ⟨_, ck6149_orbR⟩, ⟨_, ck6149_orbS⟩, ck6149_rs, ck6149_cs, ck6149_cent, ck6149_ord⟩

theorem b2_facts : B2Facts := b2Facts_of b2_hyp b2_checks

theorem b2_chain : B2Chain := b2Chain_of b2_hyp b2_checks

end CertificateChecks.ONanB2
