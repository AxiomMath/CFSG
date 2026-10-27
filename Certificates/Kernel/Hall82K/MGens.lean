module

public import Certificates.Data.Kernel.Hall82K.MGens

set_option maxRecDepth 100000

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.CGT.Hall82

theorem ch840004mg_code : zipArrK hexaMGensK hexaMGens = true := by decide +kernel

theorem ch840004mg_k : allL kPresK hexaMGensK = true := by decide +kernel

theorem ch840004mg_kmask : allN (fun v => beqB (memL v hallKList) (inKK v)) 64 = true := by
  decide +kernel

theorem ch840004mg_neg :
    zipArrK [idK, 34633937090] hexaMGens = false ∧ kPresK 1344290976 = false ∧
      kPresK idK = true := by
  decide +kernel

end CFSG.KC.Hall82K
