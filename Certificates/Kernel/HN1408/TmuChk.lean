module

public import Certificates.Kernel.HN1408.TmuData
public import Certificates.Kernel.HN1408.SpecDefs
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5
open CFSG.KLie.CT (anyN)

@[expose] noncomputable def tmY (k : Nat) : List Nat := (ykWords.getD k []).map WK

@[expose] noncomputable def tmL (k : Nat) (l : List Nat) : Nat := specK (tmY k) (l.map fun i => (i, 1))

@[expose] noncomputable def tmHd (k : Nat) (ls : List (List Nat)) (m : Nat) (G GI GJ T PL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(Nat.beq ls.length 2, bAnd(allN 2 fun j => bAnd(Nat.beq (GI j) (tmL k (ls.getD j [])),
    bAnd(Nat.beq (G j) idK, bAnd(canonK 1408 11 (mask 11) (1408 * 11) (GJ j),
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j)))),
    bAnd(Nat.beq cnt m, penumHdK idK cnt 1000 T PL)))

@[expose] noncomputable def tmRec (G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat) (cnt : Nat) :
    Bool :=
  bAnd(penumSlK 1408 11 (mask 11) (1408 * 11) true G GI 2 cnt T PL POS SRT SRI 0 cnt,
    bAnd(slK cnt (hsortPtK 1408 11 (mask 11) cnt T HS HSI) 0 cnt,
      slK (Nat.mul cnt 4) (findPtK cnt T (prodQK 1408 11 (mask 11) 4 T (bothK 2 GI GJ)) CL) 0
        (Nat.mul cnt 4)))

@[expose] noncomputable def tmCen (t : Nat) (T GI : Nat → Nat) (cnt : Nat) : Bool :=
  allN cnt fun i => strictB (T i) fun x => bIf(Nat.beq x idK, true, bIf(Nat.beq x t, true,
    bIf(bAnd(commP x (GI 0), commP x (GI 1)), false, true)))

@[expose] noncomputable def tmScan (k : Nat) (T TG : Nat → Nat) (tc : Nat) (M MG : Nat → Nat)
    (mc : Nat) (P : Nat → Nat) : Bool :=
  strictB (WK wordAZ) fun t => strictB (tmL k (uLetters.getD k [])) fun u =>
  bAnd(tmCen t T TG tc,
  bAnd(allN mc (fun i => strictB (M i) fun x => bIf(Nat.beq x idK, true, bIf(Nat.beq x t, true,
    bIf(Nat.beq (pc x x) idK, false, true)))),
  bAnd(Nat.blt (r32 P 0) tc, bAnd(Nat.beq (T (r32 P 0)) t,
  bAnd(Nat.blt (r32 P 1) tc, bAnd(Nat.beq (T (r32 P 1)) u,
  bAnd(allN 2 (fun j => bAnd(Nat.blt (r32 P (j + 2)) tc, Nat.beq (T (r32 P (j + 2))) (MG j))),
  bAnd(allN mc (fun i => bIf(Nat.beq (M i) u, false, true)),
  bAnd(involK u, bAnd(bIf(Nat.beq u t, false, true),
    bIf(commP ((tmY k).getD 0 idK) ((tmY k).getD 1 idK), false, true)))))))))))

@[expose] noncomputable def tmC8 (T : Nat → Nat) (cnt : Nat) : Bool :=
  strictB (WK wordAZ) fun t => strictB (tmL 0 (uLetters.getD 0 [])) fun u => strictB (pc t u) fun tu =>
  allN cnt fun v => strictB (T v) fun y => bIf(involK y, bIf(Nat.beq y t, true,
    anyN cnt fun i => strictB (T i) fun x => strictB (pc x y) fun xy =>
      bIf(Nat.beq xy (pc u x), true, Nat.beq xy (pc tu x))), true)

@[expose] noncomputable def tmFix : Bool :=
  strictB (tmL 1 (uLetters.getD 1 [])) fun u => strictB (WK wordAZ) fun t =>
  bAnd(allN 1408 fun p => bIf(Nat.beq (pt u p) p, false, true), anyN 1408 fun p => Nat.beq (pt t p) p)

theorem tmkHT0 : tmHd 0 (tLetters.getD 0 []) 16 TmT0.G TmT0.GI TmT0I TmT0.T TmT0.PL TmT0.cnt =
    true := by quickRfl
theorem tmkHM0 : tmHd 0 (mLetters.getD 0 []) 8 TmM0.G TmM0.GI TmM0I TmM0.T TmM0.PL TmM0.cnt =
    true := by quickRfl
theorem tmkHT1 : tmHd 1 (tLetters.getD 1 []) 16 TmT1.G TmT1.GI TmT1I TmT1.T TmT1.PL TmT1.cnt =
    true := by quickRfl
theorem tmkHM1 : tmHd 1 (mLetters.getD 1 []) 8 TmM1.G TmM1.GI TmM1I TmM1.T TmM1.PL TmM1.cnt =
    true := by quickRfl

theorem tmkRT0 : tmRec TmT0.G TmT0.GI TmT0I TmT0.T TmT0.PL TmT0.POS TmT0.SRT TmT0.SRI TmT0.HS
    TmT0.HSI TmT0Cl TmT0.cnt = true := by quickRfl
theorem tmkRM0 : tmRec TmM0.G TmM0.GI TmM0I TmM0.T TmM0.PL TmM0.POS TmM0.SRT TmM0.SRI TmM0.HS
    TmM0.HSI TmM0Cl TmM0.cnt = true := by quickRfl
theorem tmkRT1 : tmRec TmT1.G TmT1.GI TmT1I TmT1.T TmT1.PL TmT1.POS TmT1.SRT TmT1.SRI TmT1.HS
    TmT1.HSI TmT1Cl TmT1.cnt = true := by quickRfl
theorem tmkRM1 : tmRec TmM1.G TmM1.GI TmM1I TmM1.T TmM1.PL TmM1.POS TmM1.SRT TmM1.SRI TmM1.HS
    TmM1.HSI TmM1Cl TmM1.cnt = true := by quickRfl

theorem tmkS0 : tmScan 0 TmT0.T TmT0.GI 16 TmM0.T TmM0.GI 8 TmP0 = true := by quickRfl
theorem tmkS1 : tmScan 1 TmT1.T TmT1.GI 16 TmM1.T TmM1.GI 8 TmP1 = true := by quickRfl
theorem tmkC8 : tmC8 TmT0.T 16 = true := by quickRfl
theorem tmkFix : tmFix = true := by quickRfl

end CFSG.KD.HN1408

end
