module

public import Certificates.Data.Kernel.PermCent.P45Twin
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks
public import Certificates.Data.Kernel.PermCent.SealPSp43

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.P45T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum.Seal

@[expose] noncomputable def centKB (j : Nat) : Bool :=
  (((elemsCL QA45 qA45Codes).drop (j * 3240)).take 3240).all fun a =>
    !((((elemsCL QP45 qP45Codes).filter fun g =>
        eq22C g (cOf (Certificates.P43Twin.tA ())) (cOf (Certificates.P43Twin.tA ())) g).filter
          fun x => powOneC x 9).all fun x => eq22C a x x a) ||
      decide (a = 1) || decide (a = cOf (Certificates.P43Twin.tA ()))

set_option maxRecDepth 100000 in
#kc_each centKB 0 16

theorem k442003 : centKC = true := by
  unfold centKC
  rw [elemsC_eq_elemsCL qA45_strong, elemsC_eq_elemsCL qP45_strong]
  refine CFSG.KC.IdxChunks.all_chunks_of _ 3240 16 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact centKB0
  | 1, _ => exact centKB1
  | 2, _ => exact centKB2
  | 3, _ => exact centKB3
  | 4, _ => exact centKB4
  | 5, _ => exact centKB5
  | 6, _ => exact centKB6
  | 7, _ => exact centKB7
  | 8, _ => exact centKB8
  | 9, _ => exact centKB9
  | 10, _ => exact centKB10
  | 11, _ => exact centKB11
  | 12, _ => exact centKB12
  | 13, _ => exact centKB13
  | 14, _ => exact centKB14
  | 15, _ => exact centKB15
  | k + 16, h => exact absurd h (by omega)

end CFSG.Certificates.Kernel.PkCV.P45T
