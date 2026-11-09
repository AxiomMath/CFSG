module

public import Certificates.Data.A6B1
public import CFSG.GH74.KGroups.A6Inputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import Certificates.Data.Kernel.PermCent.SmallK

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Quasithin.E217A6 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.KGrp

theorem a6_4217K : a6Check (elemsV A6.QP) (elemsV A6.QA) = true := by
  rw [(elemsT_eq_elemsV A6.QP).symm.trans (elemsT_eq_elemsC A6.QP),
    (elemsT_eq_elemsV A6.QA).symm.trans (elemsT_eq_elemsC A6.QA)]
  unfold a6Check
  rw [← map_cOf_ev sList, ← map_cOf_ev p1List, eq_ev_cOf z0]
  simp only [List.all_map, List.any_map, Function.comp_def, ev_pow', ev_mul', ev_inv',
    one_eq_ev, decide_ev_eq, decide_mem_map_ev, nodup_map_ev, List.length_map, ne_eq,
    decide_not, Bool.decide_and, conj_fast, comm_fast, sq_fast, pow_fast]
  decide +kernel

end CertificateChecks.KernelKGroupsE
