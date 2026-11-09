module

public import Certificates.Kernel.Sporadic.Fi24FiveK.DataQ
public import Certificates.Kernel.Sporadic.Fi24Net.PTabSound

public section

namespace CFSG.KD.Fi24FiveK

open CFSG.KC.Fi24FiveK CFSG.KC.Fi24Base

@[expose] noncomputable def ET : List Nat → List Nat → Bool := eqB CFSG.KD.Fi24Net.letPT

theorem ET_eq : ET = E := by
  unfold ET E
  rw [CFSG.KD.Fi24Net.letPT_eq]

@[expose] noncomputable def stgT (k : Nat) : Bool := stageOK ET D.M D.C D.R k

theorem stg_eq (k : Nat) : stg k = stgT k := by
  unfold stg stgT
  rw [ET_eq]

@[expose] noncomputable def blkT (i : Nat) : Bool := blkOK ET D.R DQ.Q 33 i

theorem blk_eq (i : Nat) : blk i = blkT i := by
  unfold blk blkT
  rw [ET_eq]

end CFSG.KD.Fi24FiveK

end
