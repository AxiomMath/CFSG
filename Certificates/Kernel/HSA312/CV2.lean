module

public import Certificates.Kernel.HSA312.D
public import Certificates.Kernel.LocalQT.HS4089.L
public import Certificates.Data.Kernel.HSA312.Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsInputs
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0set_option Elab.async false

public noncomputable section

namespace CFSG.KD.HSA312

open CFSG.KC.HSA312 CFSG.Quasithin.A312Hs

@[expose] def X2 (i : Nat) : Nat := TF (Nat.add 64 i)

@[expose] def v2Code (i : Nat) : Bool :=
  explCode 1100 11 2047 (CFSG.KD.LQT.H4089.TF 0) CFSG.KD.LQT.H4089.L2c hsV2Word X2 i

theorem v2W : explW 4 64 hsV2Word = true := by quickRfl

theorem v2Dist : explDist 64 X2 = true := by quickRfl

theorem v2Conj : explConj 1100 11 2047 4 64 CFSG.KD.LQT.H4089.L2c hsV2Conj X2 = true := by
  quickRfl

end CFSG.KD.HSA312

#kss_each CFSG.KD.HSA312.CV2 CFSG.KD.HSA312.v2Code 64

end
