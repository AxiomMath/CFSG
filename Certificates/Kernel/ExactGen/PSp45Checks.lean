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

theorem kTokAll :
    ([intsL PT.chars] = PTok) ∧
    (intsOK PT.chars = true) :=
  have h := ints_of_toksCkR PT.chars PTok.head! (by decide +kernel)
  ⟨by rw [h.1]; rfl, h.2⟩

theorem kTok : [intsL PT.chars] = PTok := kTokAll.1

theorem kTokOK : intsOK PT.chars = true := kTokAll.2

theorem hbAllL :
    ((List.range 9).all (fun i => Nat.beq (SC 8 C.ctx.chP i) (CP.S i) &&
      Nat.beq (SIC 156 8 C.ctx.chP i) (CP.SI i)) = true) ∧
    (chainBindK 156 8 C.ctx.chP CP.S CP.SI 9 5 CP.BP DP = true) ∧
    (chainBindK 156 8 C.ctx.chN CN.S CN.SI 8 5 CN.BP DN = true) ∧
    (chainBindK 156 8 C.chTN CTN.S CTN.SI 5 2 CTN.BP DTN = true) ∧
    (chainBindK 156 8 C.reps[0]!.chC CC0.S CC0.SI 7 3 CC0.BP DC0 = true) ∧
    (chainBindK 156 8 C.reps[0]!.chX CX0.S CX0.SI 5 3 CX0.BP DX0 = true) ∧
    (chainBindK 156 8 C.reps[0]!.chT CT0.S CT0.SI 5 2 CT0.BP DT0 = true) ∧
    (chainBindK 156 8 C.reps[1]!.chC CC1.S CC1.SI 7 2 CC1.BP DC1 = true) ∧
    (chainBindK 156 8 C.reps[1]!.chX CX1.S CX1.SI 3 2 CX1.BP DX1 = true) ∧
    (chainBindK 156 8 C.reps[1]!.chT CT1.S CT1.SI 4 2 CT1.BP DT1 = true) ∧
    (chainBindK 156 8 C.reps[2]!.chC CC2.S CC2.SI 7 4 CC2.BP DC2 = true) ∧
    (chainBindK 156 8 C.reps[2]!.chX CX2.S CX2.SI 5 3 CX2.BP DX2 = true) ∧
    (chainBindK 156 8 C.reps[2]!.chT CT2.S CT2.SI 2 2 CT2.BP DT2 = true) ∧
    (chainBindK 156 8 C.reps[3]!.chC CC3.S CC3.SI 6 3 CC3.BP DC3 = true) ∧
    (chainBindK 156 8 C.reps[3]!.chX CX3.S CX3.SI 5 2 CX3.BP DX3 = true) ∧
    (chainBindK 156 8 C.reps[3]!.chT CT3.S CT3.SI 2 1 CT3.BP DT3 = true) := by
  decide +kernel

theorem hbAll :
    (chainBindK 156 8 C.ctx.chP CP.S CP.SI 9 5 CP.BP DP = true) ∧
    (chainBindK 156 8 C.ctx.chN CN.S CN.SI 8 5 CN.BP DN = true) ∧
    (chainBindK 156 8 C.chTN CTN.S CTN.SI 5 2 CTN.BP DTN = true) ∧
    (chainBindK 156 8 C.reps[0]!.chC CC0.S CC0.SI 7 3 CC0.BP DC0 = true) ∧
    (chainBindK 156 8 C.reps[0]!.chX CX0.S CX0.SI 5 3 CX0.BP DX0 = true) ∧
    (chainBindK 156 8 C.reps[0]!.chT CT0.S CT0.SI 5 2 CT0.BP DT0 = true) ∧
    (chainBindK 156 8 C.reps[1]!.chC CC1.S CC1.SI 7 2 CC1.BP DC1 = true) ∧
    (chainBindK 156 8 C.reps[1]!.chX CX1.S CX1.SI 3 2 CX1.BP DX1 = true) ∧
    (chainBindK 156 8 C.reps[1]!.chT CT1.S CT1.SI 4 2 CT1.BP DT1 = true) ∧
    (chainBindK 156 8 C.reps[2]!.chC CC2.S CC2.SI 7 4 CC2.BP DC2 = true) ∧
    (chainBindK 156 8 C.reps[2]!.chX CX2.S CX2.SI 5 3 CX2.BP DX2 = true) ∧
    (chainBindK 156 8 C.reps[2]!.chT CT2.S CT2.SI 2 2 CT2.BP DT2 = true) ∧
    (chainBindK 156 8 C.reps[3]!.chC CC3.S CC3.SI 6 3 CC3.BP DC3 = true) ∧
    (chainBindK 156 8 C.reps[3]!.chX CX3.S CX3.SI 5 2 CX3.BP DX3 = true) ∧
    (chainBindK 156 8 C.reps[3]!.chT CT3.S CT3.SI 2 1 CT3.BP DT3 = true) :=
  hbAllL.2

theorem hbP: chainBindK 156 8 C.ctx.chP CP.S CP.SI 9 5 CP.BP DP = true :=
  hbAll.1

theorem hbN : chainBindK 156 8 C.ctx.chN CN.S CN.SI 8 5 CN.BP DN = true :=
  hbAll.2.1

theorem hbTN : chainBindK 156 8 C.chTN CTN.S CTN.SI 5 2 CTN.BP DTN = true :=
  hbAll.2.2.1

theorem hbC0 : chainBindK 156 8 C.reps[0]!.chC CC0.S CC0.SI 7 3 CC0.BP DC0 = true :=
  hbAll.2.2.2.1

theorem hbX0 : chainBindK 156 8 C.reps[0]!.chX CX0.S CX0.SI 5 3 CX0.BP DX0 = true :=
  hbAll.2.2.2.2.1

theorem hbT0 : chainBindK 156 8 C.reps[0]!.chT CT0.S CT0.SI 5 2 CT0.BP DT0 = true :=
  hbAll.2.2.2.2.2.1

theorem hbC1 : chainBindK 156 8 C.reps[1]!.chC CC1.S CC1.SI 7 2 CC1.BP DC1 = true :=
  hbAll.2.2.2.2.2.2.1

theorem hbX1 : chainBindK 156 8 C.reps[1]!.chX CX1.S CX1.SI 3 2 CX1.BP DX1 = true :=
  hbAll.2.2.2.2.2.2.2.1

theorem hbT1 : chainBindK 156 8 C.reps[1]!.chT CT1.S CT1.SI 4 2 CT1.BP DT1 = true :=
  hbAll.2.2.2.2.2.2.2.2.1

theorem hbC2 : chainBindK 156 8 C.reps[2]!.chC CC2.S CC2.SI 7 4 CC2.BP DC2 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.1

theorem hbX2 : chainBindK 156 8 C.reps[2]!.chX CX2.S CX2.SI 5 3 CX2.BP DX2 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.2.1

theorem hbT2 : chainBindK 156 8 C.reps[2]!.chT CT2.S CT2.SI 2 2 CT2.BP DT2 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.2.2.1

theorem hbC3 : chainBindK 156 8 C.reps[3]!.chC CC3.S CC3.SI 6 3 CC3.BP DC3 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hbX3 : chainBindK 156 8 C.reps[3]!.chX CX3.S CX3.SI 5 2 CX3.BP DX3 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hbT3 : chainBindK 156 8 C.reps[3]!.chT CT3.S CT3.SI 2 1 CT3.BP DT3 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2

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

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin (strictInc)

theorem kAllF :
    ((C.ctx.chP.k = 2) ∧
    (C.ctx.chN.k = 3) ∧
    (C.chTN.k = 3) ∧
    (C.reps[0]!.chC.k = 2) ∧
    (C.reps[0]!.chX.k = 2) ∧
    (C.reps[0]!.chT.k = 4) ∧
    (C.reps[1]!.chC.k = 4) ∧
    (C.reps[1]!.chX.k = 2) ∧
    (C.reps[1]!.chT.k = 3) ∧
    (C.reps[2]!.chC.k = 3) ∧
    (C.reps[2]!.chX.k = 2) ∧
    (C.reps[2]!.chT.k = 2) ∧
    (C.reps[3]!.chC.k = 3) ∧
    (C.reps[3]!.chX.k = 3) ∧
    (C.reps[3]!.chT.k = 2) ∧
    (chainBK 156 8 C.ctx.chP = true) ∧
    (chainBK 156 8 C.ctx.chN = true) ∧
    (chainBK 156 8 C.chTN = true) ∧
    (C.reps.all (fun r => chainBK 156 8 r.chC && chainBK 156 8 r.chX &&
      chainBK 156 8 r.chT) = true) ∧
    (ctxK 156 8 C.ctx = true) ∧
    (origsK 156 8 C.chTN C.ctx.chN C.tnW = true) ∧
    (C.reps.length = 4) ∧
    (((C.ctx.chP.S[0]! == ExactGenData.psp45G1) &&
      (C.ctx.chP.S[1]! == ExactGenData.psp45G2)) = true)) ∧
    coverK 156 8 C.chTN C.ctx.chN C.tel C.reps.length
      (fun j => wK 156 8 C.ctx.chN (C.reps[j - 1]!).nuW) 128 = true ∧
    repKT 156 8 C.ctx C.reps[0]! (BT 0) 4680000 14400 7200 32
      (parOKT 156 8 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 0) 0 C.reps[0]!.par)
      (strictInc (C.reps[0]!.ord.map fun m => hashK 156 8 (BT 0 m)) ||
        strictInc (C.reps[0]!.ord.map fun m => ptKeyK 156 8 C.ctx.chN.base (BT 0 m)))
      (fixOrbK 156 8 C.ctx.chP (wK 156 8 C.ctx.chN C.reps[0]!.nuW) C.reps[0]!.par C.reps[0]!.ord
        (BT 0)) = true ∧
    repKT 156 8 C.ctx C.reps[2]! (BT 2) 4680000 15600 7800 8
      (parOKT 156 8 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 2) 0 C.reps[2]!.par)
      (strictInc (C.reps[2]!.ord.map fun m => hashK 156 8 (BT 2 m)) ||
        strictInc (C.reps[2]!.ord.map fun m => ptKeyK 156 8 C.ctx.chN.base (BT 2 m)))
      (fixOrbK 156 8 C.ctx.chP (wK 156 8 C.ctx.chN C.reps[2]!.nuW) C.reps[2]!.par C.reps[2]!.ord
        (BT 2)) = true := by
  decide +kernel

theorem kAll :
    (C.ctx.chP.k = 2) ∧
    (C.ctx.chN.k = 3) ∧
    (C.chTN.k = 3) ∧
    (C.reps[0]!.chC.k = 2) ∧
    (C.reps[0]!.chX.k = 2) ∧
    (C.reps[0]!.chT.k = 4) ∧
    (C.reps[1]!.chC.k = 4) ∧
    (C.reps[1]!.chX.k = 2) ∧
    (C.reps[1]!.chT.k = 3) ∧
    (C.reps[2]!.chC.k = 3) ∧
    (C.reps[2]!.chX.k = 2) ∧
    (C.reps[2]!.chT.k = 2) ∧
    (C.reps[3]!.chC.k = 3) ∧
    (C.reps[3]!.chX.k = 3) ∧
    (C.reps[3]!.chT.k = 2) ∧
    (chainBK 156 8 C.ctx.chP = true) ∧
    (chainBK 156 8 C.ctx.chN = true) ∧
    (chainBK 156 8 C.chTN = true) ∧
    (C.reps.all (fun r => chainBK 156 8 r.chC && chainBK 156 8 r.chX &&
      chainBK 156 8 r.chT) = true) ∧
    (ctxK 156 8 C.ctx = true) ∧
    (origsK 156 8 C.chTN C.ctx.chN C.tnW = true) ∧
    (C.reps.length = 4) ∧
    (((C.ctx.chP.S[0]! == ExactGenData.psp45G1) &&
      (C.ctx.chP.S[1]! == ExactGenData.psp45G2)) = true) :=
  kAllF.1

theorem kP: C.ctx.chP.k = 2 := kAll.1
theorem kN : C.ctx.chN.k = 3 := kAll.2.1
theorem kTN : C.chTN.k = 3 := kAll.2.2.1
theorem kC0 : C.reps[0]!.chC.k = 2 := kAll.2.2.2.1
theorem kX0 : C.reps[0]!.chX.k = 2 := kAll.2.2.2.2.1
theorem kT0 : C.reps[0]!.chT.k = 4 := kAll.2.2.2.2.2.1
theorem kC1 : C.reps[1]!.chC.k = 4 := kAll.2.2.2.2.2.2.1
theorem kX1 : C.reps[1]!.chX.k = 2 := kAll.2.2.2.2.2.2.2.1
theorem kT1 : C.reps[1]!.chT.k = 3 := kAll.2.2.2.2.2.2.2.2.1
theorem kC2 : C.reps[2]!.chC.k = 3 := kAll.2.2.2.2.2.2.2.2.2.1
theorem kX2 : C.reps[2]!.chX.k = 2 := kAll.2.2.2.2.2.2.2.2.2.2.1
theorem kT2 : C.reps[2]!.chT.k = 2 := kAll.2.2.2.2.2.2.2.2.2.2.2.1
theorem kC3 : C.reps[3]!.chC.k = 3 := kAll.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem kX3 : C.reps[3]!.chX.k = 3 := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem kT3 : C.reps[3]!.chT.k = 2 := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem f1 : chainBK 156 8 C.ctx.chP = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem f2 : chainBK 156 8 C.ctx.chN = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem f3 : chainBK 156 8 C.chTN = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem f4 : C.reps.all (fun r => chainBK 156 8 r.chC && chainBK 156 8 r.chX &&
    chainBK 156 8 r.chT) = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem f5 : ctxK 156 8 C.ctx = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem f6 : origsK 156 8 C.chTN C.ctx.chN C.tnW = true :=
  kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem f10 : coverK 156 8 C.chTN C.ctx.chN C.tel C.reps.length
    (fun j => wK 156 8 C.ctx.chN (C.reps[j - 1]!).nuW) 128 = true := kAllF.2.1
theorem f11 : C.reps.length = 4 := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem letTabP : (List.range 9).all (fun i => Nat.beq (SC 8 C.ctx.chP i) (CP.S i) &&
    Nat.beq (SIC 156 8 C.ctx.chP i) (CP.SI i)) = true :=
  hbAllL.1

theorem letEqP (l : ℤ) : letK 156 8 C.ctx.chP l = letKT 156 8 C.ctx.chP 9 CP.S CP.SI l :=
  letKT_eq 156 8 C.ctx.chP 9 CP.S CP.SI letTabP l

theorem r02 : repKT 156 8 C.ctx C.reps[0]! (BT 0) 4680000 14400 7200 32
      (parOKT 156 8 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 0) 0 C.reps[0]!.par)
      (strictInc (C.reps[0]!.ord.map fun m => hashK 156 8 (BT 0 m)) ||
        strictInc (C.reps[0]!.ord.map fun m => ptKeyK 156 8 C.ctx.chN.base (BT 0 m)))
      (fixOrbK 156 8 C.ctx.chP (wK 156 8 C.ctx.chN C.reps[0]!.nuW) C.reps[0]!.par C.reps[0]!.ord
        (BT 0)) = true ∧
    repKT 156 8 C.ctx C.reps[2]! (BT 2) 4680000 15600 7800 8
      (parOKT 156 8 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 2) 0 C.reps[2]!.par)
      (strictInc (C.reps[2]!.ord.map fun m => hashK 156 8 (BT 2 m)) ||
        strictInc (C.reps[2]!.ord.map fun m => ptKeyK 156 8 C.ctx.chN.base (BT 2 m)))
      (fixOrbK 156 8 C.ctx.chP (wK 156 8 C.ctx.chN C.reps[2]!.nuW) C.reps[2]!.par C.reps[2]!.ord
        (BT 2)) = true :=
  kAllF.2.2

theorem r0 : repK 156 8 C.ctx C.reps[0]! (BT 0) 4680000 14400 7200 32 = true :=
  (repKT_eq 156 8 C.ctx C.reps[0]! (BT 0) 4680000 14400 7200 32 _ letEqP).trans
    (repKT_or 156 8 r02.1)

theorem r2 : repK 156 8 C.ctx C.reps[2]! (BT 2) 4680000 15600 7800 8 = true :=
  (repKT_eq 156 8 C.ctx C.reps[2]! (BT 2) 4680000 15600 7800 8 _ letEqP).trans
    (repKT_or 156 8 r02.2)

@[expose] noncomputable def parR1c (j : ℕ) : List (ℕ × ℤ) := (Par1P[j]!.map Int.toNat).zip Par1L[j]!

@[expose] noncomputable def parR3c (j : ℕ) : List (ℕ × ℤ) := (Par3P[j]!.map Int.toNat).zip Par3L[j]!

@[expose] noncomputable def parR1 : List (ℕ × ℤ) :=
  parR1c 0 ++ (parR1c 1 ++ (parR1c 2 ++ (parR1c 3 ++ (parR1c 4 ++ (parR1c 5 ++ parR1c 6)))))

@[expose] noncomputable def parR3 : List (ℕ × ℤ) :=
  parR3c 0 ++ (parR3c 1 ++ (parR3c 2 ++ (parR3c 3 ++ parR3c 4)))

theorem r3M : repKT 156 8 C.ctx C.reps[3]! (BT 3) 4680000 720 180 4
      (parOKT 156 8 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 3) 0 C.reps[3]!.par)
      (strictInc (C.reps[3]!.ord.map fun m => hashK 156 8 (BT 3 m)) ||
        strictInc (C.reps[3]!.ord.map fun m => ptKeyK 156 8 C.ctx.chN.base (BT 3 m)))
      true = true ∧
    relNumK 156 8 C.ctx.relK RelRG (wK 156 8 C.ctx.chN C.reps[3]!.nuW) = 36 ∧
    (Nat.blt 36 4294967296 &&
      (List.range 156).all (fun a => Nat.beq C.ctx.rel[a]! (setKeyK 8 C.ctx.relK (RelRG a))) &&
      (List.range C.ctx.chP.k).all (fun i =>
        relMapK 156 8 C.ctx.relK RelRG (SC 8 C.ctx.chP i) &&
        relMapK 156 8 C.ctx.relK RelRG (SIC 156 8 C.ctx.chP i)) &&
      Nat.beq (setKeyK 8 36 (BT 3 0))
        (relBitsK 156 8 C.ctx.relK RelRG (wK 156 8 C.ctx.chN C.reps[3]!.nuW)) &&
      strictInc (C.reps[3]!.ord.map fun m => setKeyK 8 36 (BT 3 m))) = true ∧
    (C.reps[1]!.par == parR1 && C.reps[3]!.par == parR3) = true ∧
    (C.ctx.relP == (List.range 156).map RelRP) = true := by
  decide +kernel

theorem hTieR : (C.reps[1]!.par == parR1 && C.reps[3]!.par == parR3) = true :=
  r3M.2.2.2.1

theorem hRelRG : (fun a => C.ctx.relP[a]!) = RelRG := by
  funext a
  rw [eq_of_beq r3M.2.2.2.2, RelRG]
  cases h : Nat.blt a 156
  · have ha : ¬a < 156 := by
      rw [← Nat.blt_eq, h]
      decide
    simp [Nat.le_of_not_lt ha]
  · have ha : a < 156 := by simpa using h
    simp [ha]

theorem hTieR' : (C.reps[1]!.par == parR1) = true ∧ (C.reps[3]!.par == parR3) = true := by
  have h := hTieR
  rw [Bool.and_eq_true] at h
  exact h

theorem hParR1 : C.reps[1]!.par = parR1 := eq_of_beq hTieR'.1

theorem hParR3 : C.reps[3]!.par = parR3 := eq_of_beq hTieR'.2

theorem r1M : repKT 156 8 C.ctx C.reps[1]! (BT 1) 4680000 480 120 8
      (parOKT 156 8 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 0 C.reps[1]!.par)
      (strictInc (C.reps[1]!.ord.map fun m => hashK 156 8 (BT 1 m)) ||
        strictInc (C.reps[1]!.ord.map fun m => ptKeyK 156 8 C.ctx.chN.base (BT 1 m)))
      true = true ∧
    fixNumK 156 8 (wK 156 8 C.ctx.chN C.reps[1]!.nuW) = 12 ∧
    (Nat.blt 12 4294967296 &&
      Nat.beq (setKeyK 8 12 (BT 1 0)) (fixBitsK 156 8 (wK 156 8 C.ctx.chN C.reps[1]!.nuW)) &&
      strictInc (C.reps[1]!.ord.map fun m => setKeyK 8 12 (BT 1 m))) = true := by
  decide +kernel

theorem r1c0 : imgSetK 8 12 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 0 (parR1c 0) = true ∧
    (parR1c 0).length = 1400 := by
  decide +kernel

theorem r1c1 : imgSetK 8 12 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 1400 (parR1c 1) = true ∧
    (parR1c 1).length = 1400 := by
  decide +kernel

theorem r1c2 : imgSetK 8 12 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 2800 (parR1c 2) = true ∧
    (parR1c 2).length = 1400 := by
  decide +kernel

theorem r1c3 : imgSetK 8 12 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 4200 (parR1c 3) = true ∧
    (parR1c 3).length = 1400 := by
  decide +kernel

theorem r1c4 : imgSetK 8 12 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 5600 (parR1c 4) = true ∧
    (parR1c 4).length = 1400 := by
  decide +kernel

theorem r1c5 : imgSetK 8 12 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 7000 (parR1c 5) = true ∧
    (parR1c 5).length = 1400 := by
  decide +kernel

theorem r1c6 : imgSetK 8 12 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 8400 (parR1c 6) = true := by
  decide +kernel

theorem r1 : repK 156 8 C.ctx C.reps[1]! (BT 1) 4680000 480 120 8 = true :=
  have hp : imgSetK 8 12 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 1) 0 C.reps[1]!.par = true := by
    rw [hParR1, parR1]
    simp only [imgSetK_append, r1c0.2, r1c1.2, r1c2.2, r1c3.2, r1c4.2,
      r1c5.2, Nat.reduceAdd, r1c0.1, r1c1.1, r1c2.1, r1c3.1, r1c4.1, r1c5.1, r1c6, Bool.and_self]
  have hf : fixOrbK 156 8 C.ctx.chP (wK 156 8 C.ctx.chN C.reps[1]!.nuW) C.reps[1]!.par
      C.reps[1]!.ord (BT 1) = true :=
    fixOrbK_of 156 8 C.ctx.chP _ _ _ (BT 1) 12 r1M.2.1 _ letEqP r1M.2.2 hp
  (repKT_eq 156 8 C.ctx C.reps[1]! (BT 1) 4680000 480 120 8 _ letEqP).trans
    (repKT_or 156 8
      ((congrArg (repKT 156 8 C.ctx C.reps[1]! (BT 1) 4680000 480 120 8 _ _) hf).trans r1M.1))

theorem r3c0 : imgSetK 8 36 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 3) 0 (parR3c 0) = true ∧
    (parR3c 0).length = 1400 := by
  decide +kernel

theorem r3c1 : imgSetK 8 36 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 3) 1400 (parR3c 1) = true ∧
    (parR3c 1).length = 1400 := by
  decide +kernel

theorem r3c2 : imgSetK 8 36 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 3) 2800 (parR3c 2) = true ∧
    (parR3c 2).length = 1400 := by
  decide +kernel

theorem r3c3 : imgSetK 8 36 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 3) 4200 (parR3c 3) = true ∧
    (parR3c 3).length = 1400 := by
  decide +kernel

theorem r3c4 : imgSetK 8 36 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 3) 5600 (parR3c 4) = true := by
  decide +kernel

theorem r3 : repK 156 8 C.ctx C.reps[3]! (BT 3) 4680000 720 180 4 = true :=
  have hp : imgSetK 8 36 (letKT 156 8 C.ctx.chP 9 CP.S CP.SI) (BT 3) 0 C.reps[3]!.par = true := by
    rw [hParR3, parR3]
    simp only [imgSetK_append, r3c0.2, r3c1.2, r3c2.2, r3c3.2, Nat.reduceAdd,
      r3c0.1, r3c1.1, r3c2.1, r3c3.1, r3c4, Bool.and_self]
  have hrel : relOrbL 156 8 C.ctx.chP (wK 156 8 C.ctx.chN C.reps[3]!.nuW) C.ctx.rel C.ctx.relP
      C.ctx.relK C.reps[3]!.par C.reps[3]!.ord (BT 3) = true := by
    rw [relOrbL, hRelRG, r3M.2.1]
    exact relOrbK_of 156 8 C.ctx.chP _ C.ctx.rel C.ctx.relK RelRG 36 _ _ (BT 3)
      _ letEqP r3M.2.2.1 hp
  have hf : (fixOrbK 156 8 C.ctx.chP (wK 156 8 C.ctx.chN C.reps[3]!.nuW) C.reps[3]!.par
      C.reps[3]!.ord (BT 3) || relOrbL 156 8 C.ctx.chP (wK 156 8 C.ctx.chN C.reps[3]!.nuW)
      C.ctx.rel C.ctx.relP C.ctx.relK C.reps[3]!.par C.reps[3]!.ord (BT 3)) = true := by
    rw [hrel, Bool.or_true]
  (repKT_eq 156 8 C.ctx C.reps[3]! (BT 3) 4680000 720 180 4 _ letEqP).trans
    ((congrArg (repKT 156 8 C.ctx C.reps[3]! (BT 3) 4680000 720 180 4 _ _) hf).trans r3M.1)

theorem g01 : ((C.ctx.chP.S[0]! == ExactGenData.psp45G1) &&
    (C.ctx.chP.S[1]! == ExactGenData.psp45G2)) = true :=
  kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CertificateChecks.KernelEG.PSp45

end
