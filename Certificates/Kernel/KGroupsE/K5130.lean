module

public import CFSG.GH74.KGroups.Sz8TablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Data.Kernel.PermCent.SmallK65

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.PkCV

theorem qs_5130K : schP QS = true ∧ orderV QS = 64 := by
  constructor <;> decide +kernel

theorem bender_5130K : benderCheck (elemsV QS) tt 7 = true := by
  rw [(elemsT_eq_elemsV QS).symm.trans (elemsT_eq_elemsC QS), eq_ev_cOf tt]
  unfold benderCheck centralIn isComm
  simp only [List.all_map, List.any_map, List.filter_map, Function.comp_def, ev_pow', ev_mul', ev_inv',
    one_eq_ev, decide_ev_eq, decide_mem_map_ev, ne_eq, decide_not, Bool.decide_and, conj_fast,
    comm_fast, sq_fast, pow_fast]
  decide +kernel

theorem center_5130K :
    ((elemsV QS).filter (fun g => decide (centralIn (elemsV QS) g = true))).length = 8 := by
  decide +kernel

theorem le_5130K : (QS.original.toList.all fun g => siftP QP g 0) = true := by
  decide +kernel

theorem tt_5130K : siftP QP tt 0 = true := by
  decide +kernel

theorem neg5130K : siftP QP sg0 0 = false := by
  decide +kernel

theorem negC5130K : centralIn (elemsV QS) tt = false := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
