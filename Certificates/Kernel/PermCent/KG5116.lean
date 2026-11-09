module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK
public import CFSG.GH74.KGroups.L217Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5116

open CFSG.GH74.KGroups.L217 CFSG.Certificates.Kernel.PkEnum

theorem kQP : schP QP = true ∧ orderV QP = 2448 := by constructor <;> decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 4896 := by constructor <;> decide +kernel

theorem kOrd : orderIsC (cOf pa) 2 = true ∧ orderIsC (cOf pb) 3 = true ∧
    pairInvC ws (cOf pa) (cOf pb) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf pa) (cOf pb) = true := by
  decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf pa) (cOf pb) = true := by decide +kernel

theorem e9allC_hoist {n : Nat} [Small n] (L : List (CV n)) : e9allC L =
    (L.filter fun g => !decide (g = 1) && powOneC g 3).all fun X =>
      ((L.filter fun g => powOneC g 3).filter fun g => eq22C g X X g).all fun Y =>
        decide (Y = 1) || decide (Y = X) || decide (Y = X ^ 2) := by
  unfold e9allC
  simp only [List.filter_filter, Bool.and_comm]

theorem kE9 : e9allC (elemsC QA) = true := by
  rw [e9allC_hoist]
  decide +kernel

theorem kInner3 : inner3C (elemsC QA) QP = true := by decide +kernel

@[expose] noncomputable def kSolvB (j : Nat) : Bool :=
  (((elemsC QA).drop (j * 612)).take 612).all fun τ =>
    bif powOneC τ 2 && !decide (τ = 1) then decide ((centL (elemsC QP) τ).length ∈ [16, 18])
    else true

set_option maxRecDepth 100000 in
#kc_each kSolvB 0 8

theorem kSolv : solvC (elemsC QA) (elemsC QP) [16, 18] = true := by
  unfold solvC
  refine CFSG.KC.IdxChunks.all_chunks_of _ 612 8 _ (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact kSolvB0
  | 1, _ => exact kSolvB1
  | 2, _ => exact kSolvB2
  | 3, _ => exact kSolvB3
  | 4, _ => exact kSolvB4
  | 5, _ => exact kSolvB5
  | 6, _ => exact kSolvB6
  | 7, _ => exact kSolvB7
  | k + 8, h => exact absurd h (by omega)

theorem kCl : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf pa) x g) = true := by
  decide +kernel

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 153 := by decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 3).filter fun y =>
    pairInvC ws (cOf pa) y).length = 32 := by
  decide +kernel

theorem kCount : pairCountC (elemsC QP) 2 3 ws = 4896 := by
  rw [pairCount_conj QP (check_certificate_of _ _ _ _ _ kQP.1) 2 3 ws (cOf pa) 32 kCl kPart, kInv]

theorem kNeg : orderIsC (cOf pb) 2 = false ∧ solvC (elemsC QA) (elemsC QP) [16] = false ∧
    centTrivC (elemsC QA) 1 1 = false ∧ ((elemsC QA).all fun g => siftC QP g 0) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5116
