module

public import Certificates.Kernel.SporSch.HN.OrbXK

public section

namespace CertificateChecks.KernelSporSch.HNXOrb

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KD.LgHNX CFSG.KD.OrdHN
open CFSG.Sporadic.HNSchreier

theorem hcore' : ∀ b < 17813,
    Nat.beq (coreLeaf TX 464 1140000 MS CM3 M GA GB b (hnxC b)) (HNX.CNT b) = true :=
  CFSG.KD.HNXK.core_all

theorem hsort' : ∀ m < 17813, sortChunk TX 464 1140000 (HNX.SGT m) (hnxS m) = true :=
  CFSG.KD.HNXK.sort_all

theorem rec0_root : Nat.beq (Nat.land (getRec TX 464 0) M) V0C = true :=
  andB_left (b := Nat.beq (spread MS V0C) V0) rec0

theorem rootDigits_eq : Data.rootDigits = String.ofList (HNXRoot.c0 ++ HNXRoot.c1) := by
  rw [String.ofList_append, ← HNXRoot.e0, ← HNXRoot.e1]
  rfl

theorem checkPts_lt : ∀ q ∈ Data.checkPts.toList, q < 1140000 := by
  decide +kernel

end CertificateChecks.KernelSporSch.HNXOrb

end
