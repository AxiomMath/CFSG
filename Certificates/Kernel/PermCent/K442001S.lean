module

public import Certificates.Data.Kernel.PermCent.P45Twin
public import Certificates.Data.Kernel.PermCent.SealPSp43
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.P45T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum.Seal

@[expose] noncomputable def sylB (j : Nat) : Bool :=
  (((elemsCL QA45 qA45Codes).drop (j * 3240)).take 3240).all fun a =>
    !((elemsCL QT0 qT0Codes).all fun t => eq22C a t t a) || decide (a ∈ elemsCL QT0 qT0Codes)

set_option maxRecDepth 100000 in
#kc_each sylB 0 16

set_option maxRecDepth 100000 in
theorem sylHead : decide (((elemsCL QT0 qT0Codes).filter fun g =>
    (elemsCL QT0 qT0Codes).all fun t => eq22C g t t g).length = 2) = true := by
  decide +kernel

theorem k442001S : sylowC = true := by
  unfold sylowC
  rw [elemsC_eq_elemsCL qT0_strong, elemsC_eq_elemsCL qA45_strong]
  simp only [Bool.and_eq_true]
  refine ⟨sylHead, ?_⟩
  refine CFSG.KC.IdxChunks.all_chunks_of _ 3240 16 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact sylB0
  | 1, _ => exact sylB1
  | 2, _ => exact sylB2
  | 3, _ => exact sylB3
  | 4, _ => exact sylB4
  | 5, _ => exact sylB5
  | 6, _ => exact sylB6
  | 7, _ => exact sylB7
  | 8, _ => exact sylB8
  | 9, _ => exact sylB9
  | 10, _ => exact sylB10
  | 11, _ => exact sylB11
  | 12, _ => exact sylB12
  | 13, _ => exact sylB13
  | 14, _ => exact sylB14
  | 15, _ => exact sylB15
  | k + 16, h => exact absurd h (by omega)

end CFSG.Certificates.Kernel.PkCV.P45T
