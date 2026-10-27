module

public import Certificates.Kernel.ExactGen.PSp45ChainP
public import Certificates.Kernel.ExactGen.PSp45ChainN
public import Certificates.Kernel.ExactGen.PSp45ChainR
public import Certificates.Data.Kernel.ExactGen.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.ExactGen.PSp45Gens

public section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelEG.PSp45

open CFSG.KC.ExactGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem kTok : [intsL PT.chars] = PTok := by decide +kernel

theorem kTokOK : intsOK PT.chars = true := by decide +kernel

theorem hbP : chainBindK 156 8 C.ctx.chP CP.S CP.SI 9 5 CP.BP DP = true := by decide +kernel
theorem hbN : chainBindK 156 8 C.ctx.chN CN.S CN.SI 8 5 CN.BP DN = true := by decide +kernel
theorem hbTN : chainBindK 156 8 C.chTN CTN.S CTN.SI 5 2 CTN.BP DTN = true := by decide +kernel
theorem hbC0 : chainBindK 156 8 C.reps[0]!.chC CC0.S CC0.SI 7 3 CC0.BP DC0 = true := by
  decide +kernel
theorem hbX0 : chainBindK 156 8 C.reps[0]!.chX CX0.S CX0.SI 5 3 CX0.BP DX0 = true := by
  decide +kernel
theorem hbT0 : chainBindK 156 8 C.reps[0]!.chT CT0.S CT0.SI 5 2 CT0.BP DT0 = true := by
  decide +kernel
theorem hbC1 : chainBindK 156 8 C.reps[1]!.chC CC1.S CC1.SI 7 2 CC1.BP DC1 = true := by
  decide +kernel
theorem hbX1 : chainBindK 156 8 C.reps[1]!.chX CX1.S CX1.SI 3 2 CX1.BP DX1 = true := by
  decide +kernel
theorem hbT1 : chainBindK 156 8 C.reps[1]!.chT CT1.S CT1.SI 4 2 CT1.BP DT1 = true := by
  decide +kernel
theorem hbC2 : chainBindK 156 8 C.reps[2]!.chC CC2.S CC2.SI 7 4 CC2.BP DC2 = true := by
  decide +kernel
theorem hbX2 : chainBindK 156 8 C.reps[2]!.chX CX2.S CX2.SI 5 3 CX2.BP DX2 = true := by
  decide +kernel
theorem hbT2 : chainBindK 156 8 C.reps[2]!.chT CT2.S CT2.SI 2 2 CT2.BP DT2 = true := by
  decide +kernel
theorem hbC3 : chainBindK 156 8 C.reps[3]!.chC CC3.S CC3.SI 6 3 CC3.BP DC3 = true := by
  decide +kernel
theorem hbX3 : chainBindK 156 8 C.reps[3]!.chX CX3.S CX3.SI 5 2 CX3.BP DX3 = true := by
  decide +kernel
theorem hbT3 : chainBindK 156 8 C.reps[3]!.chT CT3.S CT3.SI 2 1 CT3.BP DT3 = true := by
  decide +kernel

theorem oP : ((List.range 5).map fun i => rcnt (CP.LR i)).prod = 4680000 := by decide +kernel
theorem oN : ((List.range 5).map fun i => rcnt (CN.LR i)).prod = 9360000 := by decide +kernel
theorem oTN : ((List.range 2).map fun i => rcnt (CTN.LR i)).prod = 128 := by decide +kernel
theorem oC0 : ((List.range 3).map fun i => rcnt (CC0.LR i)).prod = 14400 := by decide +kernel
theorem oX0 : ((List.range 3).map fun i => rcnt (CX0.LR i)).prod = 7200 := by decide +kernel
theorem oT0 : ((List.range 2).map fun i => rcnt (CT0.LR i)).prod = 32 := by decide +kernel
theorem oC1 : ((List.range 2).map fun i => rcnt (CC1.LR i)).prod = 480 := by decide +kernel
theorem oX1 : ((List.range 2).map fun i => rcnt (CX1.LR i)).prod = 120 := by decide +kernel
theorem oT1 : ((List.range 2).map fun i => rcnt (CT1.LR i)).prod = 8 := by decide +kernel
theorem oC2 : ((List.range 4).map fun i => rcnt (CC2.LR i)).prod = 15600 := by decide +kernel
theorem oX2 : ((List.range 3).map fun i => rcnt (CX2.LR i)).prod = 7800 := by decide +kernel
theorem oT2 : ((List.range 2).map fun i => rcnt (CT2.LR i)).prod = 8 := by decide +kernel
theorem oC3 : ((List.range 3).map fun i => rcnt (CC3.LR i)).prod = 720 := by decide +kernel
theorem oX3 : ((List.range 2).map fun i => rcnt (CX3.LR i)).prod = 180 := by decide +kernel
theorem oT3 : ((List.range 1).map fun i => rcnt (CT3.LR i)).prod = 4 := by decide +kernel

theorem kP : C.ctx.chP.k = 2 := by decide +kernel
theorem kN : C.ctx.chN.k = 3 := by decide +kernel
theorem kTN : C.chTN.k = 3 := by decide +kernel
theorem kC0 : C.reps[0]!.chC.k = 2 := by decide +kernel
theorem kX0 : C.reps[0]!.chX.k = 2 := by decide +kernel
theorem kT0 : C.reps[0]!.chT.k = 4 := by decide +kernel
theorem kC1 : C.reps[1]!.chC.k = 4 := by decide +kernel
theorem kX1 : C.reps[1]!.chX.k = 2 := by decide +kernel
theorem kT1 : C.reps[1]!.chT.k = 3 := by decide +kernel
theorem kC2 : C.reps[2]!.chC.k = 3 := by decide +kernel
theorem kX2 : C.reps[2]!.chX.k = 2 := by decide +kernel
theorem kT2 : C.reps[2]!.chT.k = 2 := by decide +kernel
theorem kC3 : C.reps[3]!.chC.k = 3 := by decide +kernel
theorem kX3 : C.reps[3]!.chX.k = 3 := by decide +kernel
theorem kT3 : C.reps[3]!.chT.k = 2 := by decide +kernel

theorem f1 : chainBK 156 8 C.ctx.chP = true := by decide +kernel
theorem f2 : chainBK 156 8 C.ctx.chN = true := by decide +kernel
theorem f3 : chainBK 156 8 C.chTN = true := by decide +kernel
theorem f4 : C.reps.all (fun r => chainBK 156 8 r.chC && chainBK 156 8 r.chX &&
    chainBK 156 8 r.chT) = true := by decide +kernel
theorem f5 : ctxK 156 8 C.ctx = true := by decide +kernel
theorem f6 : origsK 156 8 C.chTN C.ctx.chN C.tnW = true := by decide +kernel
theorem f10 : coverK 156 8 C.chTN C.ctx.chN C.tel C.reps.length
    (fun j => wK 156 8 C.ctx.chN (C.reps[j - 1]!).nuW) 128 = true := by decide +kernel
theorem f11 : C.reps.length = 4 := by decide +kernel

theorem r0 : repK 156 8 C.ctx C.reps[0]! (BT 0) 4680000 14400 7200 32 = true := by decide +kernel
theorem r1 : repK 156 8 C.ctx C.reps[1]! (BT 1) 4680000 480 120 8 = true := by decide +kernel
theorem r2 : repK 156 8 C.ctx C.reps[2]! (BT 2) 4680000 15600 7800 8 = true := by decide +kernel
theorem r3 : repK 156 8 C.ctx C.reps[3]! (BT 3) 4680000 720 180 4 = true := by decide +kernel

theorem g01 : ((C.ctx.chP.S[0]! == ExactGenData.psp45G1) &&
    (C.ctx.chP.S[1]! == ExactGenData.psp45G2)) = true := by decide +kernel

end CertificateChecks.KernelEG.PSp45

end
