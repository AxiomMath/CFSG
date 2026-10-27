module

public import Certificates.Kernel.ExactGen.J2ChainP
public import Certificates.Kernel.ExactGen.J2ChainN
public import Certificates.Kernel.ExactGen.J2ChainR
public import Certificates.Data.Kernel.ExactGen.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelEG.J2

open CFSG.KC.ExactGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem kTok : [intsL J2T.chars] = J2Tok := by decide +kernel

theorem kTokOK : intsOK J2T.chars = true := by decide +kernel

theorem hbP : chainBindK 315 9 C.ctx.chP CP.S CP.SI 7 3 CP.BP DP = true := by decide +kernel
theorem hbN : chainBindK 315 9 C.ctx.chN CN.S CN.SI 9 3 CN.BP DN = true := by decide +kernel
theorem hbTN : chainBindK 315 9 C.chTN CTN.S CTN.SI 4 2 CTN.BP DTN = true := by decide +kernel
theorem hbC0 : chainBindK 315 9 C.reps[0]!.chC CC0.S CC0.SI 5 3 CC0.BP DC0 = true := by
  decide +kernel
theorem hbX0 : chainBindK 315 9 C.reps[0]!.chX CX0.S CX0.SI 4 3 CX0.BP DX0 = true := by
  decide +kernel
theorem hbT0 : chainBindK 315 9 C.reps[0]!.chT CT0.S CT0.SI 3 1 CT0.BP DT0 = true := by
  decide +kernel
theorem hbC1 : chainBindK 315 9 C.reps[1]!.chC CC1.S CC1.SI 6 2 CC1.BP DC1 = true := by
  decide +kernel
theorem hbX1 : chainBindK 315 9 C.reps[1]!.chX CX1.S CX1.SI 2 1 CX1.BP DX1 = true := by
  decide +kernel
theorem hbT1 : chainBindK 315 9 C.reps[1]!.chT CT1.S CT1.SI 2 1 CT1.BP DT1 = true := by
  decide +kernel
theorem hbC2 : chainBindK 315 9 C.reps[2]!.chC CC2.S CC2.SI 4 2 CC2.BP DC2 = true := by
  decide +kernel
theorem hbX2 : chainBindK 315 9 C.reps[2]!.chX CX2.S CX2.SI 3 2 CX2.BP DX2 = true := by
  decide +kernel
theorem hbT2 : chainBindK 315 9 C.reps[2]!.chT CT2.S CT2.SI 3 2 CT2.BP DT2 = true := by
  decide +kernel

theorem oP : ((List.range 3).map fun i => rcnt (CP.LR i)).prod = 604800 := by decide +kernel
theorem oN : ((List.range 3).map fun i => rcnt (CN.LR i)).prod = 1209600 := by decide +kernel
theorem oTN : ((List.range 2).map fun i => rcnt (CTN.LR i)).prod = 256 := by decide +kernel
theorem oC0 : ((List.range 3).map fun i => rcnt (CC0.LR i)).prod = 1920 := by decide +kernel
theorem oX0 : ((List.range 3).map fun i => rcnt (CX0.LR i)).prod = 1920 := by decide +kernel
theorem oT0 : ((List.range 1).map fun i => rcnt (CT0.LR i)).prod = 128 := by decide +kernel
theorem oC1 : ((List.range 2).map fun i => rcnt (CC1.LR i)).prod = 240 := by decide +kernel
theorem oX1 : ((List.range 1).map fun i => rcnt (CX1.LR i)).prod = 60 := by decide +kernel
theorem oT1 : ((List.range 1).map fun i => rcnt (CT1.LR i)).prod = 4 := by decide +kernel
theorem oC2 : ((List.range 2).map fun i => rcnt (CC2.LR i)).prod = 336 := by decide +kernel
theorem oX2 : ((List.range 2).map fun i => rcnt (CX2.LR i)).prod = 168 := by decide +kernel
theorem oT2 : ((List.range 2).map fun i => rcnt (CT2.LR i)).prod = 8 := by decide +kernel

theorem f1 : chainBK 315 9 C.ctx.chP = true := by decide +kernel
theorem f2 : chainBK 315 9 C.ctx.chN = true := by decide +kernel
theorem f3 : chainBK 315 9 C.chTN = true := by decide +kernel
theorem f4 : C.reps.all (fun r => chainBK 315 9 r.chC && chainBK 315 9 r.chX &&
    chainBK 315 9 r.chT) = true := by decide +kernel
theorem f5 : ctxK 315 9 C.ctx = true := by decide +kernel
theorem f6 : origsK 315 9 C.chTN C.ctx.chN C.tnW = true := by decide +kernel
theorem f10 : coverK 315 9 C.chTN C.ctx.chN C.tel C.reps.length
    (fun j => wK 315 9 C.ctx.chN (C.reps[j - 1]!).nuW) 256 = true := by decide +kernel
theorem f11 : C.reps.length = 3 := by decide +kernel

theorem r0 : repK 315 9 C.ctx C.reps[0]! (BT 0) 604800 1920 1920 128 = true := by decide +kernel
theorem r1 : repK 315 9 C.ctx C.reps[1]! (BT 1) 604800 240 60 4 = true := by decide +kernel
theorem r2 : repK 315 9 C.ctx C.reps[2]! (BT 2) 604800 336 168 8 = true := by decide +kernel

theorem kP : C.ctx.chP.k = 2 := by decide +kernel
theorem kN : C.ctx.chN.k = 3 := by decide +kernel
theorem kTN : C.chTN.k = 3 := by decide +kernel
theorem kC0 : C.reps[0]!.chC.k = 2 := by decide +kernel
theorem kX0 : C.reps[0]!.chX.k = 2 := by decide +kernel
theorem kT0 : C.reps[0]!.chT.k = 3 := by decide +kernel
theorem kC1 : C.reps[1]!.chC.k = 4 := by decide +kernel
theorem kX1 : C.reps[1]!.chX.k = 2 := by decide +kernel
theorem kT1 : C.reps[1]!.chT.k = 2 := by decide +kernel
theorem kC2 : C.reps[2]!.chC.k = 3 := by decide +kernel
theorem kX2 : C.reps[2]!.chX.k = 2 := by decide +kernel
theorem kT2 : C.reps[2]!.chT.k = 2 := by decide +kernel

end CertificateChecks.KernelEG.J2

end
