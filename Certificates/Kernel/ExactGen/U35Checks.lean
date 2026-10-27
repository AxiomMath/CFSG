module

public import Certificates.Kernel.ExactGen.U35Chain
public import Certificates.Data.Kernel.ExactGen.Defs
public import Certificates.Data.HNUnitaryBridge
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelEG.U35

open CFSG.KC.ExactGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem kTok : [intsL PT.chars] = PTok := by decide +kernel

theorem kTokOK : intsOK PT.chars = true := by decide +kernel

theorem hbP : chainBindK 50 6 C.ctx.chP CP.S CP.SI 11 4 CP.BP DP = true := by decide +kernel
theorem hbN : chainBindK 50 6 C.ctx.chN CN.S CN.SI 12 4 CN.BP DN = true := by decide +kernel
theorem hbTN : chainBindK 50 6 C.chTN CTN.S CTN.SI 5 2 CTN.BP DTN = true := by decide +kernel
theorem hbC0 : chainBindK 50 6 C.reps[0]!.chC CC0.S CC0.SI 4 2 CC0.BP DC0 = true := by
  decide +kernel
theorem hbX0 : chainBindK 50 6 C.reps[0]!.chX CX0.S CX0.SI 3 2 CX0.BP DX0 = true := by
  decide +kernel
theorem hbT0 : chainBindK 50 6 C.reps[0]!.chT CT0.S CT0.SI 2 1 CT0.BP DT0 = true := by
  decide +kernel
theorem hbC1 : chainBindK 50 6 C.reps[1]!.chC CC1.S CC1.SI 5 3 CC1.BP DC1 = true := by
  decide +kernel
theorem hbX1 : chainBindK 50 6 C.reps[1]!.chX CX1.S CX1.SI 3 2 CX1.BP DX1 = true := by
  decide +kernel
theorem hbT1 : chainBindK 50 6 C.reps[1]!.chT CT1.S CT1.SI 2 1 CT1.BP DT1 = true := by
  decide +kernel

theorem oP : ((List.range 4).map fun i => rcnt (CP.LR i)).prod = 126000 := by decide +kernel
theorem oN : ((List.range 4).map fun i => rcnt (CN.LR i)).prod = 252000 := by decide +kernel
theorem oTN : ((List.range 2).map fun i => rcnt (CTN.LR i)).prod = 32 := by decide +kernel
theorem oC0 : ((List.range 2).map fun i => rcnt (CC0.LR i)).prod = 240 := by decide +kernel
theorem oX0 : ((List.range 2).map fun i => rcnt (CX0.LR i)).prod = 120 := by decide +kernel
theorem oT0 : ((List.range 1).map fun i => rcnt (CT0.LR i)).prod = 8 := by decide +kernel
theorem oC1 : ((List.range 3).map fun i => rcnt (CC1.LR i)).prod = 120 := by decide +kernel
theorem oX1 : ((List.range 2).map fun i => rcnt (CX1.LR i)).prod = 60 := by decide +kernel
theorem oT1 : ((List.range 1).map fun i => rcnt (CT1.LR i)).prod = 4 := by decide +kernel

theorem kP : C.ctx.chP.k = 6 := by decide +kernel
theorem kN : C.ctx.chN.k = 7 := by decide +kernel
theorem kTN : C.chTN.k = 5 := by decide +kernel
theorem kC0 : C.reps[0]!.chC.k = 2 := by decide +kernel
theorem kX0 : C.reps[0]!.chX.k = 2 := by decide +kernel
theorem kT0 : C.reps[0]!.chT.k = 2 := by decide +kernel
theorem kC1 : C.reps[1]!.chC.k = 3 := by decide +kernel
theorem kX1 : C.reps[1]!.chX.k = 2 := by decide +kernel
theorem kT1 : C.reps[1]!.chT.k = 2 := by decide +kernel

theorem f1 : chainBK 50 6 C.ctx.chP = true := by decide +kernel
theorem f2 : chainBK 50 6 C.ctx.chN = true := by decide +kernel
theorem f3 : chainBK 50 6 C.chTN = true := by decide +kernel
theorem f4 : C.reps.all (fun r => chainBK 50 6 r.chC && chainBK 50 6 r.chX &&
    chainBK 50 6 r.chT) = true := by decide +kernel
theorem f5 : ctxK 50 6 C.ctx = true := by decide +kernel
theorem f6 : origsK 50 6 C.chTN C.ctx.chN C.tnW = true := by decide +kernel
theorem f10 : coverK 50 6 C.chTN C.ctx.chN C.tel C.reps.length
    (fun j => wK 50 6 C.ctx.chN (C.reps[j - 1]!).nuW) 32 = true := by decide +kernel
theorem f11 : C.reps.length = 2 := by decide +kernel

theorem r0 : repK 50 6 C.ctx C.reps[0]! (BT 0) 126000 240 120 8 = true := by decide +kernel
theorem r1 : repK 50 6 C.ctx C.reps[1]! (BT 1) 126000 120 60 4 = true := by decide +kernel

theorem g01 : (C.ctx.chP.S.extract 0 6 == HNUnitaryBridge.smallPerms) = true := by decide +kernel

end CertificateChecks.KernelEG.U35

end
