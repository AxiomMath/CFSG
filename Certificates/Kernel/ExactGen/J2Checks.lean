module

public import Certificates.Kernel.ExactGen.J2ChainP
public import Certificates.Kernel.ExactGen.J2ChainN
public import Certificates.Kernel.ExactGen.J2ChainR
public import Certificates.Data.Kernel.ExactGen.Defs
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Kernel.ExactGen.J2Data

namespace CertificateChecks.KernelEG.J2

meta def parWJ (j : Nat) : Array (List Int) :=
  #[fcM.reps[j]!.par.map fun pl => (16 * pl.1 + pl.2 + 8 : Int)]

meta def ordWJ (j : Nat) : Array (List Int) := #[fcM.reps[j]!.ord.map fun m => (m : Int)]

meta def parWJ1 : Array (List Int) := parWJ 1
meta def ordWJ1 : Array (List Int) := ordWJ 1

end CertificateChecks.KernelEG.J2

public section

#kc_intwords CertificateChecks.KernelEG.J2.ParWJ1 CertificateChecks.KernelEG.J2.parWJ1
#kc_intwords CertificateChecks.KernelEG.J2.OrdWJ1 CertificateChecks.KernelEG.J2.ordWJ1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelEG.J2

open CFSG.KC.ExactGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin (strictInc)

theorem kTokAll :
    ([intsL J2T.chars] = J2Tok) ∧
    (intsOK J2T.chars = true) :=
  have h := ints_of_toksCkR J2T.chars J2Tok.head! (by decide +kernel)
  ⟨by rw [h.1]; rfl, h.2⟩

theorem kTok : [intsL J2T.chars] = J2Tok := kTokAll.1

theorem kTokOK : intsOK J2T.chars = true := kTokAll.2

@[expose] noncomputable def decParJ (z : ℤ) : ℕ × ℤ := (z.toNat / 16, ((z.toNat % 16 : ℕ) : ℤ) - 8)

@[expose] noncomputable def parLJ1 : List (ℕ × ℤ) := ParWJ1.head!.map decParJ

@[expose] noncomputable def ordLJ1 : List ℕ := OrdWJ1.head!.map Int.toNat

theorem cOnce :
    ((chainBindK 315 9 C.ctx.chP CP.S CP.SI 7 3 CP.BP DP = true) ∧
    (chainBindK 315 9 C.ctx.chN CN.S CN.SI 9 3 CN.BP DN = true) ∧
    (chainBindK 315 9 C.chTN CTN.S CTN.SI 4 2 CTN.BP DTN = true) ∧
    (chainBindK 315 9 C.reps[0]!.chC CC0.S CC0.SI 5 3 CC0.BP DC0 = true) ∧
    (chainBindK 315 9 C.reps[0]!.chX CX0.S CX0.SI 4 3 CX0.BP DX0 = true) ∧
    (chainBindK 315 9 C.reps[0]!.chT CT0.S CT0.SI 3 1 CT0.BP DT0 = true) ∧
    (chainBindK 315 9 C.reps[1]!.chC CC1.S CC1.SI 6 2 CC1.BP DC1 = true) ∧
    (chainBindK 315 9 C.reps[1]!.chX CX1.S CX1.SI 2 1 CX1.BP DX1 = true) ∧
    (chainBindK 315 9 C.reps[1]!.chT CT1.S CT1.SI 2 1 CT1.BP DT1 = true) ∧
    (chainBindK 315 9 C.reps[2]!.chC CC2.S CC2.SI 4 2 CC2.BP DC2 = true) ∧
    (chainBindK 315 9 C.reps[2]!.chX CX2.S CX2.SI 3 2 CX2.BP DX2 = true) ∧
    (chainBindK 315 9 C.reps[2]!.chT CT2.S CT2.SI 3 2 CT2.BP DT2 = true)) ∧
    ((C.ctx.chP.k = 2) ∧
    (C.ctx.chN.k = 3) ∧
    (C.chTN.k = 3) ∧
    (C.reps[0]!.chC.k = 2) ∧
    (C.reps[0]!.chX.k = 2) ∧
    (C.reps[0]!.chT.k = 3) ∧
    (C.reps[1]!.chC.k = 4) ∧
    (C.reps[1]!.chX.k = 2) ∧
    (C.reps[1]!.chT.k = 2) ∧
    (C.reps[2]!.chC.k = 3) ∧
    (C.reps[2]!.chX.k = 2) ∧
    (C.reps[2]!.chT.k = 2) ∧
    (C.reps.length = 3) ∧
    (chainBK 315 9 C.ctx.chP = true) ∧
    (chainBK 315 9 C.ctx.chN = true) ∧
    (chainBK 315 9 C.chTN = true) ∧
    (C.reps.all
      (fun r => chainBK 315 9 r.chC && chainBK 315 9 r.chX && chainBK 315 9 r.chT) = true) ∧
    (ctxK 315 9 C.ctx = true) ∧
    (origsK 315 9 C.chTN C.ctx.chN C.tnW = true)) ∧
    ((List.range 7).all (fun i => Nat.beq (SC 9 C.ctx.chP i) (CP.S i) &&
      Nat.beq (SIC 315 9 C.ctx.chP i) (CP.SI i)) = true) ∧
    (C.reps[1]!.par = parLJ1 ∧ C.reps[1]!.ord = ordLJ1 ∧ C.ctx.chN.base = [1, 0, 2]) ∧
    (repKT 315 9 C.ctx C.reps[1]! (BT 1) 604800 240 60 4 true true
        (fixOrbK 315 9 C.ctx.chP (wK 315 9 C.ctx.chN C.reps[1]!.nuW) C.reps[1]!.par
          C.reps[1]!.ord (BT 1)) = true ∧
      C.reps[1]!.par.length ≤ 4 * 630) := by
  decide +kernel

theorem hbAll :
    (chainBindK 315 9 C.ctx.chP CP.S CP.SI 7 3 CP.BP DP = true) ∧
    (chainBindK 315 9 C.ctx.chN CN.S CN.SI 9 3 CN.BP DN = true) ∧
    (chainBindK 315 9 C.chTN CTN.S CTN.SI 4 2 CTN.BP DTN = true) ∧
    (chainBindK 315 9 C.reps[0]!.chC CC0.S CC0.SI 5 3 CC0.BP DC0 = true) ∧
    (chainBindK 315 9 C.reps[0]!.chX CX0.S CX0.SI 4 3 CX0.BP DX0 = true) ∧
    (chainBindK 315 9 C.reps[0]!.chT CT0.S CT0.SI 3 1 CT0.BP DT0 = true) ∧
    (chainBindK 315 9 C.reps[1]!.chC CC1.S CC1.SI 6 2 CC1.BP DC1 = true) ∧
    (chainBindK 315 9 C.reps[1]!.chX CX1.S CX1.SI 2 1 CX1.BP DX1 = true) ∧
    (chainBindK 315 9 C.reps[1]!.chT CT1.S CT1.SI 2 1 CT1.BP DT1 = true) ∧
    (chainBindK 315 9 C.reps[2]!.chC CC2.S CC2.SI 4 2 CC2.BP DC2 = true) ∧
    (chainBindK 315 9 C.reps[2]!.chX CX2.S CX2.SI 3 2 CX2.BP DX2 = true) ∧
    (chainBindK 315 9 C.reps[2]!.chT CT2.S CT2.SI 3 2 CT2.BP DT2 = true) :=
  cOnce.1

theorem hbP : chainBindK 315 9 C.ctx.chP CP.S CP.SI 7 3 CP.BP DP = true := hbAll.1

theorem hbN : chainBindK 315 9 C.ctx.chN CN.S CN.SI 9 3 CN.BP DN = true := hbAll.2.1

theorem hbTN : chainBindK 315 9 C.chTN CTN.S CTN.SI 4 2 CTN.BP DTN = true := hbAll.2.2.1

theorem hbC0 : chainBindK 315 9 C.reps[0]!.chC CC0.S CC0.SI 5 3 CC0.BP DC0 = true := hbAll.2.2.2.1

theorem hbX0 : chainBindK 315 9 C.reps[0]!.chX CX0.S CX0.SI 4 3 CX0.BP DX0 = true := hbAll.2.2.2.2.1

theorem hbT0 : chainBindK 315 9 C.reps[0]!.chT CT0.S CT0.SI 3 1 CT0.BP DT0 = true :=
  hbAll.2.2.2.2.2.1

theorem hbC1 : chainBindK 315 9 C.reps[1]!.chC CC1.S CC1.SI 6 2 CC1.BP DC1 = true :=
  hbAll.2.2.2.2.2.2.1

theorem hbX1 : chainBindK 315 9 C.reps[1]!.chX CX1.S CX1.SI 2 1 CX1.BP DX1 = true :=
  hbAll.2.2.2.2.2.2.2.1

theorem hbT1 : chainBindK 315 9 C.reps[1]!.chT CT1.S CT1.SI 2 1 CT1.BP DT1 = true :=
  hbAll.2.2.2.2.2.2.2.2.1

theorem hbC2 : chainBindK 315 9 C.reps[2]!.chC CC2.S CC2.SI 4 2 CC2.BP DC2 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.1

theorem hbX2 : chainBindK 315 9 C.reps[2]!.chX CX2.S CX2.SI 3 2 CX2.BP DX2 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.2.1

theorem hbT2 : chainBindK 315 9 C.reps[2]!.chT CT2.S CT2.SI 3 2 CT2.BP DT2 = true :=
  hbAll.2.2.2.2.2.2.2.2.2.2.2

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


theorem kAll :
    (C.ctx.chP.k = 2) ∧
    (C.ctx.chN.k = 3) ∧
    (C.chTN.k = 3) ∧
    (C.reps[0]!.chC.k = 2) ∧
    (C.reps[0]!.chX.k = 2) ∧
    (C.reps[0]!.chT.k = 3) ∧
    (C.reps[1]!.chC.k = 4) ∧
    (C.reps[1]!.chX.k = 2) ∧
    (C.reps[1]!.chT.k = 2) ∧
    (C.reps[2]!.chC.k = 3) ∧
    (C.reps[2]!.chX.k = 2) ∧
    (C.reps[2]!.chT.k = 2) ∧
    (C.reps.length = 3) ∧
    (chainBK 315 9 C.ctx.chP = true) ∧
    (chainBK 315 9 C.ctx.chN = true) ∧
    (chainBK 315 9 C.chTN = true) ∧
    (C.reps.all
      (fun r => chainBK 315 9 r.chC && chainBK 315 9 r.chX && chainBK 315 9 r.chT) = true) ∧
    (ctxK 315 9 C.ctx = true) ∧
    (origsK 315 9 C.chTN C.ctx.chN C.tnW = true) :=
  cOnce.2.1

theorem kP : C.ctx.chP.k = 2 := kAll.1

theorem kN : C.ctx.chN.k = 3 := kAll.2.1

theorem kTN : C.chTN.k = 3 := kAll.2.2.1

theorem kC0 : C.reps[0]!.chC.k = 2 := kAll.2.2.2.1

theorem kX0 : C.reps[0]!.chX.k = 2 := kAll.2.2.2.2.1

theorem kT0 : C.reps[0]!.chT.k = 3 := kAll.2.2.2.2.2.1

theorem kC1 : C.reps[1]!.chC.k = 4 := kAll.2.2.2.2.2.2.1

theorem kX1 : C.reps[1]!.chX.k = 2 := kAll.2.2.2.2.2.2.2.1

theorem kT1 : C.reps[1]!.chT.k = 2 := kAll.2.2.2.2.2.2.2.2.1

theorem kC2 : C.reps[2]!.chC.k = 3 := kAll.2.2.2.2.2.2.2.2.2.1

theorem kX2 : C.reps[2]!.chX.k = 2 := kAll.2.2.2.2.2.2.2.2.2.2.1

theorem kT2 : C.reps[2]!.chT.k = 2 := kAll.2.2.2.2.2.2.2.2.2.2.2.1

theorem f11 : C.reps.length = 3 := kAll.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem f1 : chainBK 315 9 C.ctx.chP = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem f2 : chainBK 315 9 C.ctx.chN = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem f3 : chainBK 315 9 C.chTN = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem f4 : C.reps.all (fun r => chainBK 315 9 r.chC && chainBK 315 9 r.chX &&
    chainBK 315 9 r.chT) = true :=
  kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem f5 : ctxK 315 9 C.ctx = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem f6 : origsK 315 9 C.chTN C.ctx.chN C.tnW = true := kAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem f10 : coverK 315 9 C.chTN C.ctx.chN C.tel C.reps.length
    (fun j => wK 315 9 C.ctx.chN (C.reps[j - 1]!).nuW) 256 = true := by decide +kernel

theorem letTabP : (List.range 7).all (fun i => Nat.beq (SC 9 C.ctx.chP i) (CP.S i) &&
    Nat.beq (SIC 315 9 C.ctx.chP i) (CP.SI i)) = true :=
  cOnce.2.2.1

theorem letEqP (l : ℤ) : letK 315 9 C.ctx.chP l = letKT 315 9 C.ctx.chP 7 CP.S CP.SI l :=
  letKT_eq 315 9 C.ctx.chP 7 CP.S CP.SI letTabP l

theorem r0Fx : repKT 315 9 C.ctx C.reps[0]! (BT 0) 604800 1920 1920 128
      (parOKT 315 9 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 0) 0 C.reps[0]!.par)
      (strictInc (C.reps[0]!.ord.map fun m => hashK 315 9 (BT 0 m)) ||
        strictInc (C.reps[0]!.ord.map fun m => ptKeyK 315 9 C.ctx.chN.base (BT 0 m)))
      true = true ∧
    fixNumK 315 9 (wK 315 9 C.ctx.chN C.reps[0]!.nuW) = 11 ∧
    (Nat.blt 11 4294967296 &&
      Nat.beq (setKeyK 9 11 (BT 0 0)) (fixBitsK 315 9 (wK 315 9 C.ctx.chN C.reps[0]!.nuW)) &&
      strictInc (C.reps[0]!.ord.map fun m => setKeyK 9 11 (BT 0 m))) = true ∧
    imgSetK 9 11 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 0) 0 C.reps[0]!.par = true := by
  decide +kernel

theorem r0 : repK 315 9 C.ctx C.reps[0]! (BT 0) 604800 1920 1920 128 = true :=
  have hf : fixOrbK 315 9 C.ctx.chP (wK 315 9 C.ctx.chN C.reps[0]!.nuW) C.reps[0]!.par
      C.reps[0]!.ord (BT 0) = true :=
    fixOrbK_of 315 9 C.ctx.chP _ _ _ (BT 0) 11 r0Fx.2.1 _ letEqP r0Fx.2.2.1 r0Fx.2.2.2
  (repKT_eq 315 9 C.ctx C.reps[0]! (BT 0) 604800 1920 1920 128 _ letEqP).trans
    (repKT_or 315 9
      ((congrArg (repKT 315 9 C.ctx C.reps[0]! (BT 0) 604800 1920 1920 128 _ _) hf).trans r0Fx.1))

theorem repLJ : C.reps[1]!.par = parLJ1 ∧ C.reps[1]!.ord = ordLJ1 ∧
    C.ctx.chN.base = [1, 0, 2] :=
  cOnce.2.2.2.1

theorem r1M : repKT 315 9 C.ctx C.reps[1]! (BT 1) 604800 240 60 4 true true
      (fixOrbK 315 9 C.ctx.chP (wK 315 9 C.ctx.chN C.reps[1]!.nuW) C.reps[1]!.par
        C.reps[1]!.ord (BT 1)) = true ∧
    C.reps[1]!.par.length ≤ 4 * 630 :=
  cOnce.2.2.2.2

theorem r1K0 : strictInc ((ordLJ1.map fun m => ptKeyK 315 9 [1, 0, 2] (BT 1 m)).take (1260 + 1)) =
    true := by
  decide +kernel

theorem r1K1 : strictInc ((ordLJ1.map fun m => ptKeyK 315 9 [1, 0, 2] (BT 1 m)).drop 1260) =
    true := by
  decide +kernel

theorem r1K : (strictInc (C.reps[1]!.ord.map fun m => hashK 315 9 (BT 1 m)) ||
    strictInc (C.reps[1]!.ord.map fun m => ptKeyK 315 9 C.ctx.chN.base (BT 1 m))) = true := by
  rw [repLJ.2.1, repLJ.2.2, strictInc_split 1260 _ r1K0 r1K1, Bool.or_true]

theorem r1c0 : parOKT 315 9 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 1) (0 + 0 * 630)
    ((parLJ1.drop (0 * 630)).take 630) = true := by
  decide +kernel

theorem r1c1 : parOKT 315 9 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 1) (0 + 1 * 630)
    ((parLJ1.drop (1 * 630)).take 630) = true := by
  decide +kernel

theorem r1c2 : parOKT 315 9 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 1) (0 + 2 * 630)
    ((parLJ1.drop (2 * 630)).take 630) = true := by
  decide +kernel

theorem r1c3 : parOKT 315 9 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 1) (0 + 3 * 630)
    ((parLJ1.drop (3 * 630)).take 630) = true := by
  decide +kernel

theorem r1 : repK 315 9 C.ctx C.reps[1]! (BT 1) 604800 240 60 4 = true :=
  have hl := (congrArg (fun l : List (ℕ × ℤ) => l.length ≤ 4 * 630) repLJ.1).mp r1M.2
  have hq := parOKT_chunks 315 9 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 1) 630 4 0 _ hl
    fun j hj => match j, hj with
      | 0, _ => r1c0
      | 1, _ => r1c1
      | 2, _ => r1c2
      | 3, _ => r1c3
      | _ + 4, h => absurd h (by omega)
  have hp := (congrArg (fun l => parOKT 315 9 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 1) 0 l =
    true) repLJ.1).mpr hq
  (repKT_eq 315 9 C.ctx C.reps[1]! (BT 1) 604800 240 60 4 _ letEqP).trans
    (repKT_or 315 9 ((congrArg₂ (fun pb hb => repKT 315 9 C.ctx C.reps[1]! (BT 1) 604800 240 60 4
      pb hb (fixOrbK 315 9 C.ctx.chP (wK 315 9 C.ctx.chN C.reps[1]!.nuW) C.reps[1]!.par
        C.reps[1]!.ord (BT 1))) hp r1K).trans r1M.1))

theorem r2Fx : repKT 315 9 C.ctx C.reps[2]! (BT 2) 604800 336 168 8
      (parOKT 315 9 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 2) 0 C.reps[2]!.par)
      (strictInc (C.reps[2]!.ord.map fun m => hashK 315 9 (BT 2 m)) ||
        strictInc (C.reps[2]!.ord.map fun m => ptKeyK 315 9 C.ctx.chN.base (BT 2 m)))
      true = true ∧
    fixNumK 315 9 (wK 315 9 C.ctx.chN C.reps[2]!.nuW) = 21 ∧
    (Nat.blt 21 4294967296 &&
      Nat.beq (setKeyK 9 21 (BT 2 0)) (fixBitsK 315 9 (wK 315 9 C.ctx.chN C.reps[2]!.nuW)) &&
      strictInc (C.reps[2]!.ord.map fun m => setKeyK 9 21 (BT 2 m))) = true ∧
    imgSetK 9 21 (letKT 315 9 C.ctx.chP 7 CP.S CP.SI) (BT 2) 0 C.reps[2]!.par = true := by
  decide +kernel

theorem r2 : repK 315 9 C.ctx C.reps[2]! (BT 2) 604800 336 168 8 = true :=
  have hf : fixOrbK 315 9 C.ctx.chP (wK 315 9 C.ctx.chN C.reps[2]!.nuW) C.reps[2]!.par
      C.reps[2]!.ord (BT 2) = true :=
    fixOrbK_of 315 9 C.ctx.chP _ _ _ (BT 2) 21 r2Fx.2.1 _ letEqP r2Fx.2.2.1 r2Fx.2.2.2
  (repKT_eq 315 9 C.ctx C.reps[2]! (BT 2) 604800 336 168 8 _ letEqP).trans
    (repKT_or 315 9
      ((congrArg (repKT 315 9 C.ctx C.reps[2]! (BT 2) 604800 336 168 8 _ _) hf).trans r2Fx.1))

end CertificateChecks.KernelEG.J2

end
