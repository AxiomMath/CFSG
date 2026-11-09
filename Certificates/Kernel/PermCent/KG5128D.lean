module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8Inputs
public import Certificates.Data.Kernel.PermCent.SealSz8
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5128

open CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkEnum.Seal

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 455 := by
  simp only [elemsC, sz8QP_strong]
  decide +kernel

theorem kConj : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf pa) x g) = true := by
  simp only [elemsC, sz8QP_strong]
  decide +kernel

@[expose] def kPartN (j : Nat) : Nat := [11, 6, 15, 16, 16, 16, 17, 7, 12, 11, 7, 15, 15, 12, 3, 13].getD j 0

set_option maxRecDepth 100000 in
theorem kPartP0 : ((((elemsCL QP sz8QPCodes).drop (0 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP1 : ((((elemsCL QP sz8QPCodes).drop (1 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP2 : ((((elemsCL QP sz8QPCodes).drop (2 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP3 : ((((elemsCL QP sz8QPCodes).drop (3 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP4 : ((((elemsCL QP sz8QPCodes).drop (4 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP5 : ((((elemsCL QP sz8QPCodes).drop (5 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP6 : ((((elemsCL QP sz8QPCodes).drop (6 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP7 : ((((elemsCL QP sz8QPCodes).drop (7 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 7 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP8 : ((((elemsCL QP sz8QPCodes).drop (8 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP9 : ((((elemsCL QP sz8QPCodes).drop (9 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 9 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP10 : ((((elemsCL QP sz8QPCodes).drop (10 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 10 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP11 : ((((elemsCL QP sz8QPCodes).drop (11 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 11 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP12 : ((((elemsCL QP sz8QPCodes).drop (12 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP13 : ((((elemsCL QP sz8QPCodes).drop (13 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP14 : ((((elemsCL QP sz8QPCodes).drop (14 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kPartP15 : ((((elemsCL QP sz8QPCodes).drop (15 * 1820)).take 1820).filter fun y =>
    pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN 15 := by
  decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 4).filter fun y =>
    pairInvC ws (cOf pa) y).length = 192 := by
  rw [elemsC_eq_elemsCL sz8QP_strong, List.filter_filter,
    CFSG.KC.IdxChunks.length_filter_chunks _ 1820 16 _ (by decide +kernel)]
  have h : ∀ j ∈ List.range 16, ((((elemsCL QP sz8QPCodes).drop (j * 1820)).take 1820).filter fun y =>
      pairInvC ws (cOf pa) y && orderIsC y 4).length = kPartN j := by
    intro j hj
    have hj' := List.mem_range.1 hj
    match j, hj' with
    | 0, _ => exact kPartP0
    | 1, _ => exact kPartP1
    | 2, _ => exact kPartP2
    | 3, _ => exact kPartP3
    | 4, _ => exact kPartP4
    | 5, _ => exact kPartP5
    | 6, _ => exact kPartP6
    | 7, _ => exact kPartP7
    | 8, _ => exact kPartP8
    | 9, _ => exact kPartP9
    | 10, _ => exact kPartP10
    | 11, _ => exact kPartP11
    | 12, _ => exact kPartP12
    | 13, _ => exact kPartP13
    | 14, _ => exact kPartP14
    | 15, _ => exact kPartP15
    | k + 16, h => exact absurd h (by omega)
  rw [List.map_congr_left h]
  decide


theorem kNegD : ((elemsC QP).any fun g => eq22C g (cOf pa) (cOf pb) g) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5128
