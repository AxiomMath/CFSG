module

public import Certificates.Kernel.ONanF2.Data

public section

namespace CFSG.KC.ONanF2.Checks

open CFSG.KC.ONanF2 CFSG.KC.ONanF2K CFSG.OddStandard.ONanRec.F2

theorem chCentre : allB (fun x => !(cmK 16 x && cmK 4 x && cmK 1 x && cmK 64 x && cmK 256 x) ||
    (Nat.beq x 0 || Nat.beq x 34)) 512 = true := by
  decide +kernel

theorem chInv : Nat.beq (maskOf (fun u => Nat.beq (mulK u u) 0 && !Nat.beq u 0) 512) mInv = true := by
  decide +kernel

theorem chInvCnt : Nat.beq (cntM mInv 512) 87 = true := by decide +kernel

theorem chInvCover : Nat.beq (diffM mInv (Nat.lor (mCls 0) (Nat.lor (mCls 1) (Nat.lor (mCls 2)
    (Nat.lor (mCls 3) (Nat.lor (mCls 4) (Nat.lor (mCls 5) (mCls 6)))))))) 0 = true := by
  decide +kernel

theorem chClsDisj : ∀ i j : Fin 7, i ≠ j → Nat.land (mCls i) (mCls j) = 0 := by decide +kernel

theorem chCls : ∀ i : Fin 7,
    clsOKB pairsE (invC i) (mCls i) (![1, 2, 4, 16, 32, 16, 16] i) = true := by
  decide +kernel

theorem chCentr : ∀ i : Fin 7,
    cntQ (fun g => cmK g (invC i)) 512 = ![512, 256, 128, 32, 16, 32, 32] i := by
  decide +kernel

theorem chNv1 : nvB pairsE nvL1 = true := by decide +kernel
theorem chNv2 : nvB pairsE nvL2 = true := by decide +kernel
theorem chNv3 : nvB pairsE nvL3 = true := by decide +kernel

theorem chNvCover : Nat.beq (diffM (Nat.sub (Nat.shiftLeft 1 512) (Nat.shiftLeft 1 64))
    (Nat.lor (lorP nvL1) (Nat.lor (lorP nvL2) (lorP nvL3)))) 0 = true := by
  decide +kernel

theorem chV0 : subB gV0L mV0 32 = true := by decide +kernel
theorem chPd : subB gPdL mPd 64 = true := by decide +kernel
theorem chComm : subB gCommL mPd 64 = true := by decide +kernel
theorem chV : subB gVL mV 64 = true := by decide +kernel
theorem chW : subB gWL mW 8 = true := by decide +kernel
theorem chVt : subB gVtL mVt 128 = true := by decide +kernel
theorem chQ : subB gQL mQ 32 = true := by decide +kernel
theorem chR : subB gRL mR 16 = true := by decide +kernel
theorem chMax : ∀ i : Fin 7, subB (gMaxL i) (mMax i) 256 = true := by decide +kernel
theorem chCent : ∀ i : Fin 3, subB (gCentL i) (mCent i) 32 = true := by decide +kernel
theorem chCV : ∀ i : Fin 7, subB (gCVL i) (mCV i) (cardCV i) = true := by decide +kernel

theorem chMaxT : ∀ i j : Fin 7, Nat.blt 0 (Nat.land (mMax i) (mCls j)) = maxTable i j := by
  decide +kernel

theorem chQR1 : Nat.beq (Nat.land mQ mR) 1 = true := by decide +kernel

theorem chRL : Nat.beq (lorL rL 0) mR = true := by decide +kernel

theorem chQR2 : Nat.beq (imgM (rmulK rL) mQ 512) (Nat.sub (Nat.shiftLeft 1 512) 1) = true := by
  decide +kernel

theorem chQR3 : Nat.beq (diffM (Nat.land mQ mInv) (Nat.lor (mCls 1) (Nat.lor (mCls 2) (mCls 4))))
    0 = true := by
  decide +kernel

theorem chQR4 : Nat.beq (Nat.land mR mInv) (setB 0 34) = true := by decide +kernel

theorem chCentC : ∀ i : Fin 3, maskOf (fun g => cmK g (![131, 256, 268] i)) 512 = mCent i := by
  decide +kernel

theorem chCentCount : ∀ i : Fin 3, ∀ j : Fin 7,
    cntM (Nat.land (mCent i) (Nat.land mInv (mCls j))) 512 = centCount i j := by
  decide +kernel

theorem chCVt : Nat.beq (maskOf (fun g => cmK g 8) 512) mVt = true := by decide +kernel
theorem chCM0 : Nat.beq (maskOf (fun g => cmK g 17) 512) (mMax 0) = true := by decide +kernel
theorem chCM1 : Nat.beq (maskOf (fun g => cmK g 27) 512) (mMax 1) = true := by decide +kernel

theorem chDer : Nat.beq mPd (Nat.land (mMax 0) (Nat.land (mMax 1) (mMax 3))) = true := by
  decide +kernel

theorem chOrd : allB ordB 512 = true := by decide +kernel

theorem chCVc : ∀ i : Fin 7, allB (fun g => !Nat.beq (dC g) 0 || iffB (condCV i (dec g))
    (bitB (mCV i) g)) 512 = true := by
  decide +kernel

theorem chW1 : Nat.beq (maskOf (fun x => Nat.beq (dC x) 0 && Nat.beq (mulK x x) 0) 512) mW = true := by
  decide +kernel

theorem chW2 : allB (fun g => iffB (cmK g 32 && cmK g 8 && cmK g 2) (Nat.beq (dC g) 0)) 512 = true := by
  decide +kernel

theorem chW3 : allB (fun g => iffB (cmK g 16 && cmK g 4 && cmK g 1) (Nat.beq (dC g) 0)) 512 = true := by
  decide +kernel

theorem chWL : Nat.beq (lorL wL 0) mW = true := by decide +kernel

theorem chW4 : allB (fun g => wConjB g (invK g)) 512 = true := by
  decide +kernel

end CFSG.KC.ONanF2.Checks
