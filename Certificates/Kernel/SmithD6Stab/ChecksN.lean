module

public import Certificates.Data.Kernel.SmithD6.Trees
public import Certificates.Data.Kernel.SmithD6.StabData
public import Certificates.Data.Kernel.SmithD6.StabN
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

open CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab

#kc_each CertificateChecks.SmithD6Stab d6scn (fun c => clsChunkOKN J.lineKeysC S.clsCntC c) 0 179

#kc_each CertificateChecks.SmithD6Stab d6srn (fun c => repOK lineTree c) 0 6

public section

namespace CertificateChecks.SmithD6Stab

#kc_forall_chunks clsChunksN_ok (fun c => clsChunkOKN J.lineKeysC S.clsCntC c = true)
  179 CertificateChecks.SmithD6Stab.d6scn 1

#kc_forall_chunks reps_ok (fun c => repOK lineTree c = true) 6 CertificateChecks.SmithD6Stab.d6srn 1

theorem clsCntC_length : S.clsCntC.length = 179 := by decide +kernel

theorem clsCntC_sum : S.clsCntC.sum =
    1 + 810 * 2 ^ 19 + 768 * 2 ^ 38 + 25200 * 2 ^ 57 + 207360 * 2 ^ 76 + 131072 * 2 ^ 95 := by
  decide +kernel

theorem lineKeysC_head : J.lineKeysC.flatten[0]? = some 4098 := by decide +kernel

end CertificateChecks.SmithD6Stab

end
