
module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L34AutInputs
public import Certificates.Data.Kernel.PermCent.SemiReg
public import Certificates.Data.Kernel.PermCent.Seal
public import Certificates.Data.Kernel.PermCent.SealU33L34
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5123

open CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkEnum.Seal

@[expose] noncomputable def scA : List (VP 42) := l34QACodes.map (mkVP 42)

@[expose] noncomputable def l0E : List (Fin 42 × VP 42) :=
  (levelV scA QA.base ⟨0, by decide⟩).entries

theorem kQA0len : l0E.length ≤ 4 * 11 := by decide +kernel

theorem kQA0c0 : ((l0E.drop (0 * 11)).take 11).all
    (schStep scA QA.base ⟨0, by decide⟩) = true := by
  decide +kernel

theorem kQA0c1 : ((l0E.drop (1 * 11)).take 11).all
    (schStep scA QA.base ⟨0, by decide⟩) = true := by
  decide +kernel

theorem kQA0c2 : ((l0E.drop (2 * 11)).take 11).all
    (schStep scA QA.base ⟨0, by decide⟩) = true := by
  decide +kernel

theorem kQA0c3 : ((l0E.drop (3 * 11)).take 11).all
    (schStep scA QA.base ⟨0, by decide⟩) = true := by
  decide +kernel

theorem kQA0 : schLev scA QA.base ⟨0, by decide⟩ = true :=
  CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 11 4 kQA0len fun j hj =>
    match j, hj with
    | 0, _ => kQA0c0
    | 1, _ => kQA0c1
    | 2, _ => kQA0c2
    | 3, _ => kQA0c3
    | k + 4, h => absurd h (by omega)

theorem kQA1 : schLev scA QA.base ⟨1, by decide⟩ = true := by
  decide +kernel

theorem kQA2 : schLev scA QA.base ⟨2, by decide⟩ = true := by
  decide +kernel

theorem kQA3 : schLev scA QA.base ⟨3, by decide⟩ = true := by
  decide +kernel

theorem kQA4 : schLev scA QA.base ⟨4, by decide⟩ = true := by
  decide +kernel

theorem kQA5 : schLev scA QA.base ⟨5, by decide⟩ = true := by
  decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 241920 := by
  simp only [schP, orderV, l34QA_strong]
  refine ⟨schV_of (by decide +kernel) fun i => ?_, by decide +kernel⟩
  obtain ⟨i, hi⟩ := i
  have h6 : QA.baseCount = 6 := rfl
  match i, hi with
  | 0, _ => exact kQA0
  | 1, _ => exact kQA1
  | 2, _ => exact kQA2
  | 3, _ => exact kQA3
  | 4, _ => exact kQA4
  | 5, _ => exact kQA5
  | j + 6, h => exact absurd h (by omega)

@[expose] def l34R : List Nat := [0, 21]

@[expose] def l34Rho : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

@[expose] def l34W : List (List Bool) :=
  [[], [true, true, false], [true, false, true, true], [false, true, false, true, true, true, false], [true, false], [true], [true, true, false, true, true, true, false], [false], [false, true], [false, true, true, true], [true, true, false, true, true, true], [false, true, false], [true, true], [true, true, true, false], [true, false, true], [true, false, true, true, true, false], [true, true, true], [false, true, true], [true, false, true, true, true], [false, true, false, true, true], [false, true, true, true, false], [], [true, true, false], [true, false, true], [true, true, true, false], [true, false, true, true], [true, true, true], [true, true, false, true, false], [false], [false, true, true, true], [false, true, true], [true, true, true, false, true], [true, false, true, false], [false, true, false], [false, true], [true, true, false, true], [false, true, true, true, false], [true, true], [true, false], [true, false, true, true, true], [false, true, false, true], [true]]

@[expose] def l34Wit : List (Nat × Bool) :=
  [(0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (3, true), (3, true), (3, true), (3, true), (1, false), (1, false), (1, false), (1, false), (3, true), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (3, true), (3, true), (3, true), (3, true), (25, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (25, false), (25, false), (25, false), (25, false), (22, false), (22, false), (22, false), (22, false), (0, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (22, false), (25, false), (25, false), (25, false), (25, false)]

set_option maxRecDepth 100000 in
theorem l34Semi : SemiReg.semiregChk 42 (img 42 (cOf PA).1) (img 42 (cOf PB).1) l34R l34Rho l34W
    l34Wit = true := by
  decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf PA) (cOf PB) = true :=
  SemiReg.centTrivC_of_semireg _ _ _ l34Semi

theorem kQA_neg : orderV QA ≠ 120960 := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5123
