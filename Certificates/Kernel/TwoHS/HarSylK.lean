module

public import Certificates.Kernel.TwoHS.HarSylD
public import Certificates.Data.Kernel.PosWalk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.PosWalk CFSG.KC.Loop

@[expose] noncomputable def syGW : List (List Nat) :=
  [[1, 0, 1, 1, 2, 0, 2, 0, 2, 0, 2, 1, 2, 5, 3, 5, 4, 4, 3, 4, 5, 4, 5, 3, 5, 3],
   [1, 0, 1, 2, 0, 2, 2, 1, 0, 2, 1, 0, 1, 2, 2, 5, 5, 3, 5, 4, 3, 4, 5, 5, 4, 3, 4, 5, 3, 4],
   [1, 2, 1, 2, 2, 0, 0, 2, 1, 0, 2, 2, 0, 2, 3, 5, 5, 4, 5, 4, 5, 3, 5, 5, 3, 4, 5, 3],
   [0, 2, 1, 2, 1, 5, 4, 5, 3, 4],
   [0, 2, 1, 1, 2, 2, 0, 1, 2, 2, 2, 1, 5, 5, 4, 4, 5, 3, 4, 5, 5, 5, 4, 3],
   [0], [1, 2, 2]]

@[expose] noncomputable def syGet (j : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih j => Nat.rec (motive := fun _ => List Nat) a (fun j' _ => ih j') j) syGW j

@[expose] noncomputable def syWalk (l x : Nat) : Nat := walkK TECl 6 (syGet l) x

@[expose] noncomputable def syTreeAt (P Par Lab : Nat → Nat) (ng i : Nat) : Bool :=
  bIf(Nat.beq i 0, Nat.beq (r32 P 0) 0,
    strictB (r32 Par i) (fun p => strictB (r32 Lab i) (fun l =>
      bAnd(Nat.blt p i, bAnd(Nat.blt l ng, Nat.beq (syWalk l (r32 P p)) (r32 P i))))))

@[expose] noncomputable def syClosedAt (P PI : Nat → Nat) (ng m i : Nat) : Bool :=
  strictB (r32 P i) (fun q => bAnd(Nat.blt q 1024, bAnd(Nat.beq (r32 PI q) i,
    allN ng (fun l => strictB (syWalk l q) (fun q' => Nat.blt (r32 PI q') m)))))

@[expose] noncomputable def syInvAt (P PI : Nat → Nat) (m q : Nat) : Bool :=
  strictB (r32 PI q) (fun e => bIf(Nat.blt e m, Nat.beq (r32 P e) q, true))

@[expose] noncomputable def syMul (x y : Nat) : Nat := pathPosK TECl 6 TE.PL 1024 x y

@[expose] noncomputable def syT : Nat := walkK TECl 6 [0, 1, 0, 1, 2, 0, 1, 0, 1, 2] 0

@[expose] noncomputable def syZ1 : Nat := walkK TECl 6 [2, 2, 2, 2] 0

@[expose] noncomputable def syZ2 : Nat := walkK TECl 6 [2, 2, 2, 2] syT

@[expose] noncomputable def sySqCnt (P : Nat → Nat) (m z : Nat) : Nat :=
  cntK m (fun i => strictB (r32 P i) (fun x => Nat.beq (syMul x x) z))

@[expose] noncomputable def sySqCntE (z : Nat) : Nat := cntK 1024 (fun x => Nat.beq (syMul x x) z)

theorem ch26131_treeC : allN 128 (syTreeAt CPos CPar CLab 5) = true := by quickRfl
theorem ch26131_treeW : allN 512 (syTreeAt WPos WPar WLab 7) = true := by quickRfl
theorem ch26131_clC : allN 128 (syClosedAt CPos CPI 5 128) = true := by quickRfl
theorem ch26131_clW : allN 512 (syClosedAt WPos WPI 7 512) = true := by quickRfl
theorem ch26131_invC : allN 1024 (syInvAt CPos CPI 128) = true := by quickRfl
theorem ch26131_invW : allN 1024 (syInvAt WPos WPI 512) = true := by quickRfl

theorem ch26131_pts : bAnd(Nat.blt syT 1024, bAnd(Nat.blt syZ1 1024, bAnd(Nat.blt syZ2 1024,
    bAnd(Nat.beq (syMul syT syT) 0, bAnd(Nat.beq (syMul syZ1 syZ1) 0,
    bAnd(bIf(Nat.beq syT 0, false, true), bAnd(bIf(Nat.beq syZ1 0, false, true),
    bAnd(bIf(Nat.beq syZ2 0, false, true), bAnd(bIf(Nat.beq syZ1 syT, false, true),
    bAnd(bIf(Nat.beq syZ2 syT, false, true), bIf(Nat.beq syZ2 syZ1, false, true))))))))))) =
    true := by
  quickRfl

theorem ch26131_pts2 : bAnd(Nat.blt (r32 CPI syT) 128,
    allN 3 (fun j => Nat.beq (wstepK TECl 6 syZ1 j) (syMul (wstepK TECl 6 0 j) syZ1))) = true := by
  quickRfl

theorem ch26131_sqE : bAnd(Nat.beq (sySqCntE syT) 80, bAnd(Nat.beq (sySqCntE syZ1) 64,
    Nat.beq (sySqCntE syZ2) 48)) = true := by
  quickRfl

theorem ch26131_sqC : bAnd(Nat.beq (sySqCnt CPos 128 syT) 16, bAnd(Nat.beq (sySqCnt CPos 128 syZ1) 32,
    Nat.beq (sySqCnt CPos 128 syZ2) 16)) = true := by
  quickRfl

theorem ch26131_sqW : bAnd(Nat.beq (sySqCnt WPos 512 syT) 48, Nat.beq (sySqCnt WPos 512 syZ2) 16) =
    true := by
  quickRfl

theorem ch26131_cent : Nat.beq (cntK 1024 (fun x =>
    allN 3 (fun j => Nat.beq (wstepK TECl 6 x j) (syMul (wstepK TECl 6 0 j) x)))) 4 = true := by
  quickRfl

theorem ch26131_inv : allN 1024 (fun x => bIf(Nat.beq (syMul x x) 0, Nat.blt (r32 WPI x) 512, true)) =
    true := by
  quickRfl

end CFSG.KD.TwoHS

end
