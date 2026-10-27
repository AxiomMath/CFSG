module

public import Certificates.Kernel.ONanMirror.Checks
public import Certificates.Kernel.ONanB2.Glue
public import CFSG.Certificates.Kernel.ONanMirrorKSound

public section

namespace CertificateChecks.ONanMirror

open CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.MirK CertificateChecks.ONanB2

theorem mirror_facts : MirrorFactsP := mirrorFactsP_of b2_hyp ck6150_small

theorem mirror_rels : ∀ r ∈ relsM, FreeGroup.lift gen2Perm r = 1 := relsP_of b2_hyp ck6150_small

theorem mirror_chainP : MirrorChainP :=
  mirrorChainP_of b2_hyp ck6149_fz ck6150_ff ⟨_, ck6150_orb⟩ ck6150_cent ck6150_t0 ck6150_chain0
    ck6150_chain1

end CertificateChecks.ONanMirror
