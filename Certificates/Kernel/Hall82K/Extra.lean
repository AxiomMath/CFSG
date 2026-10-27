module

public import Certificates.Data.Kernel.Hall82K.Affine

public section

namespace CFSG.KC.Hall82K

theorem ch840004ex_rminv : allL (fun r => Nat.beq (compL r r) idK) rmK = true := by
  decide +kernel

theorem ch840004ex_c5fix : allL (fun w => Nat.beq (apL (Nat.land w m36K) 5) 5) c5K = true := by
  decide +kernel

theorem ch840004ex_neg :
    allL (fun r => Nat.beq (compL r r) idK) [4439643498] = false ∧
      allL (fun w => Nat.beq (apL (Nat.land w m36K) 5) 5) [1344290976] = false := by
  decide +kernel

end CFSG.KC.Hall82K
