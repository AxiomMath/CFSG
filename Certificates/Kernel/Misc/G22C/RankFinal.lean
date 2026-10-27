module

public import CFSG.Certificates.Kernel.Misc.G22RSound
public import Certificates.Kernel.Misc.G22C.Final
public import Certificates.Kernel.Misc.G22C.Rank

public section

namespace CFSG.KD.G22C

open CFSG.Quasithin.H13.KGCert CFSG.KD.G22W

theorem cert7115_ok : g22RankCheck = true :=
  CFSG.KC.G22C.rank_check g22c_facts.1 (fun t _ => CFSG.KC.G22W.recX_lt REC 2 t) g22c_facts.2
    g22c_reps.1 g22c_reps.2 g22c_conj_ok (by norm_num) g22c_class0_ok g22c_class1_ok g22c_rank0_ok
    g22c_rank1_ok

end CFSG.KD.G22C

end
