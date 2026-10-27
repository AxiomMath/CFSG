module

public import Certificates.Data.Kernel.Hall82K.C5

set_option maxRecDepth 100000

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa

theorem ch840004c5_srch : c5SrchK c5LinK 6 0 = true := by decide +kernel

theorem ch840004c5_oval : allL (fun w => ovalOkK (Nat.land w m36K)) c5K = true := by
  decide +kernel

theorem ch840004c5_neg :
    c5SrchK c5LinK.tail 6 0 = false ∧ ovalOkK 1344290976 = false ∧ ovalOkK idK = true := by
  decide +kernel

end CFSG.KC.Hall82K
