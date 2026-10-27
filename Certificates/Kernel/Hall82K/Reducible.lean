module

public import Certificates.Data.Kernel.Hall82K.Defs
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

namespace CFSG.KC.Hall82K

#kc_each ch840004red r (fun x => bor (Nat.beq (bitN q0K x) 1) (srchK 5 x)) 1 64

theorem ch840004red_neg_good3 :
    band (goodK 51607634434) (good2K 51607634434) = true ∧ good3K 51607634434 = false := by
  decide +kernel

theorem ch840004red_neg_w : wInvK 51607634434 = false ∧ wInvK 34630287489 = true := by
  decide +kernel

theorem ch840004red_neg_mem : memL 51607634434 s40K = false ∧ memL 35243180167 s40K = true := by
  decide +kernel

theorem ch840004red_neg_bits :
    forBitsK (fun x => Nat.blt x 62) 64 (candK 0 0) = false ∧
      forBitsK (fun x => Nat.blt x 63) 64 (candK 0 0) = true ∧
      forBitsK (fun _ => true) 34 (candK 0 0) = false ∧
      forBitsK (fun _ => true) 35 (candK 0 0) = true := by
  decide +kernel

end CFSG.KC.Hall82K
