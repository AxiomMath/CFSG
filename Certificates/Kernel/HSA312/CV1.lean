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

@[expose] def X1 (i : Nat) : Nat := TF i

@[expose] def v1Code (i : Nat) : Bool :=
  explCode 1100 11 2047 (CFSG.KD.LQT.H4089.TF 0) CFSG.KD.LQT.H4089.L1c hsV1Word X1 i

theorem v1W : explW 4 64 hsV1Word = true := by quickRfl

theorem v1Dist : explDist 64 X1 = true := by quickRfl

theorem v1Conj : explConj 1100 11 2047 4 64 CFSG.KD.LQT.H4089.L1c hsV1Conj X1 = true := by
  quickRfl

end CFSG.KD.HSA312

#kss_each CFSG.KD.HSA312.CV1 CFSG.KD.HSA312.v1Code 64

end
