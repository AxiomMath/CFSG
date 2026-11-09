module

public import Certificates.Data.Kernel.PermCent.B0Twin
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks
public import Certificates.Data.Kernel.PermCent.SealPSp43

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.B0T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaB0
  CFSG.Certificates.Kernel.PkEnum.Seal

@[expose] noncomputable def kCentB (j : Nat) : Bool :=
  (((elemsCL QA45 qA45Codes).drop (j * 3240)).take 3240).all fun a =>
    !(blC.all fun b => eq22C a b b a) || decide (a ∈ blC)

set_option maxRecDepth 100000 in
#kc_each kCentB 0 16

theorem kCent : centC (elemsC QA45) blC = true := by
  rw [elemsC_eq_elemsCL qA45_strong]
  unfold centC
  refine CFSG.KC.IdxChunks.all_chunks_of _ 3240 16 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact kCentB0
  | 1, _ => exact kCentB1
  | 2, _ => exact kCentB2
  | 3, _ => exact kCentB3
  | 4, _ => exact kCentB4
  | 5, _ => exact kCentB5
  | 6, _ => exact kCentB6
  | 7, _ => exact kCentB7
  | 8, _ => exact kCentB8
  | 9, _ => exact kCentB9
  | 10, _ => exact kCentB10
  | 11, _ => exact kCentB11
  | 12, _ => exact kCentB12
  | 13, _ => exact kCentB13
  | 14, _ => exact kCentB14
  | 15, _ => exact kCentB15
  | k + 16, h => exact absurd h (by omega)

theorem kClass : classC (elemsC QP45) phC (allVecs ()) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.B0T
