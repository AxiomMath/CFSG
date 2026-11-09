module

public import CFSG.GH74.GLS.Prop27.OddCoreCheck
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import CFSG.GH74.KGroups.L28Inputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Data.Kernel.PermCent.SmallK

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkCV

theorem odd_5095K : CFSG.GH74.GLS.Prop27.oddCoreCheck 189 (elemsV L28.QA) (elemsV L28.QP) = true := by
  rw [(elemsT_eq_elemsV L28.QA).symm.trans (elemsT_eq_elemsC L28.QA),
    (elemsT_eq_elemsV L28.QP).symm.trans (elemsT_eq_elemsC L28.QP)]
  unfold CFSG.GH74.GLS.Prop27.oddCoreCheck CFSG.GH74.GLS.Prop27.oddCoreAt
  simp only [List.all_map, List.any_map, List.filter_map, Function.comp_def, ev_pow', ev_mul', ev_inv',
    one_eq_ev, decide_ev_eq, decide_mem_map_ev, ne_eq, decide_not, Bool.decide_and, conj_fast,
    comm_fast, sq_fast, pow_fast]
  decide +kernel

end CertificateChecks.KernelKGroupsE
