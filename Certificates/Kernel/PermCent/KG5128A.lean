module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8Inputs
public import Certificates.Data.Kernel.PermCent.SealSz8

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5128

open CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkEnum.Seal

theorem kQP : schP QP = true ∧ orderV QP = 29120 := by
  simp only [schP, orderV, sz8QP_strong]
  constructor <;> decide +kernel

theorem kQA0 : schLev (sz8QACodes.map (mkVP 65)) QA.base ⟨0, by decide⟩ = true := by
  decide +kernel

theorem kQA1 : schLev (sz8QACodes.map (mkVP 65)) QA.base ⟨1, by decide⟩ = true := by
  decide +kernel

theorem kQA2 : schLev (sz8QACodes.map (mkVP 65)) QA.base ⟨2, by decide⟩ = true := by
  decide +kernel

theorem kQA3 : schLev (sz8QACodes.map (mkVP 65)) QA.base ⟨3, by decide⟩ = true := by
  decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 87360 := by
  simp only [schP, orderV, sz8QA_strong]
  refine ⟨schV_of (by decide +kernel) fun i => ?_, by decide +kernel⟩
  obtain ⟨i, hi⟩ := i
  have h4 : QA.baseCount = 4 := rfl
  match i, hi with
  | 0, _ => exact kQA0
  | 1, _ => exact kQA1
  | 2, _ => exact kQA2
  | 3, _ => exact kQA3
  | j + 4, h => exact absurd h (by omega)

theorem kOrd : orderIsC (cOf pa) 2 = true ∧ orderIsC (cOf pb) 4 = true ∧
    pairInvC ws (cOf pa) (cOf pb) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf pa) (cOf pb) = true := by
  decide +kernel

theorem kNegA : orderV QA ≠ 29120 ∧ orderIsC (cOf pb) 2 = false ∧ siftC QP (cOf sg0) 0 = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5128
