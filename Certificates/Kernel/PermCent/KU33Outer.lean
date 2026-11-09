module

public import Certificates.Data.Kernel.PermCent.OuterRepOC
public import Certificates.Data.Kernel.PermCent.SylowListC
public import CFSG.GH74.KGroups.U33TablesInputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import Certificates.Data.Kernel.PermCent.SealU33L34

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.U33R.KOut

open CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkCV.SylL CFSG.Certificates.Kernel.PkCV.OutR
  CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkEnum.Seal

@[expose] noncomputable def gP : List (CV 28) := [cOf pa, cOf pb]

@[expose] noncomputable def gS : List (CV 28) := [cOf sy0, cOf sy1, cOf sy2, cOf sy3, cOf sy4]

@[expose] noncomputable def tO : CV 28 := cOf pt2

@[expose] noncomputable def tI : CV 28 := cOf pu

@[expose] noncomputable def inP (x : CV 28) : Bool := siftC QP x 0

@[expose] def csOW : List (List Nat) :=
  [[1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]]

@[expose] noncomputable def csO : List (CV 28) := csOW.map (wordC gP)

@[expose] def csIW : List (List Nat) := [[0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0]]

@[expose] noncomputable def csI : List (CV 28) := csIW.map (wordC gP)

@[expose] noncomputable def bl : CV 28 := wordC gP [1, 0, 1, 0, 1, 0, 1, 1, 0, 0]

@[expose] noncomputable def bc₁ : CV 28 := wordC gP [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]

@[expose] noncomputable def bc₂ : CV 28 := wordC gP [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]

@[expose] noncomputable def wa : CV 28 := wordC gP [1]

@[expose] noncomputable def wb : CV 28 := wordC gP [0, 0, 1, 1, 0]

@[expose] noncomputable def e3 : CV 28 := wordC gP [0, 1, 0, 0]

@[expose] def refsW : List (List Nat) :=
  [[1], [1, 1, 0, 1, 0, 0, 1], [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1]]

@[expose] noncomputable def refs : List (CV 28) := refsW.map (wordC gP)

@[expose] def ksW : List (List Nat) := [[], [1, 0, 1, 0, 1, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 0, 1, 0, 0]]

@[expose] noncomputable def ks : List (CV 28) := ksW.map (wordC gP)

@[expose] noncomputable def inPS (x : CV 28) : Bool :=
  siftV (levelsV (u33QPCodes.map (mkVP 28)) QP.base 0) (codeV (ev x))

theorem inP_eq : inP = inPS := by
  funext x
  unfold inP inPS siftC
  rw [u33QP_strong]

@[expose] noncomputable def pPass (ψ : CV 28) : Bool :=
  outT csO tO ψ && innerT csI tI ψ && centT (elemsCL QS u33QSCodes) gS ψ &&
    sqOT inPS (elemsCL QS u33QSCodes) gS ψ

theorem kPassLen : (elemsCL QA u33QACodes).length ≤ 16 * 756 := by decide +kernel

theorem kPass0 : (((elemsCL QA u33QACodes).drop (0 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass1 : (((elemsCL QA u33QACodes).drop (1 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass2 : (((elemsCL QA u33QACodes).drop (2 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass3 : (((elemsCL QA u33QACodes).drop (3 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass4 : (((elemsCL QA u33QACodes).drop (4 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass5 : (((elemsCL QA u33QACodes).drop (5 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass6 : (((elemsCL QA u33QACodes).drop (6 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass7 : (((elemsCL QA u33QACodes).drop (7 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass8 : (((elemsCL QA u33QACodes).drop (8 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass9 : (((elemsCL QA u33QACodes).drop (9 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass10 : (((elemsCL QA u33QACodes).drop (10 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass11 : (((elemsCL QA u33QACodes).drop (11 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass12 : (((elemsCL QA u33QACodes).drop (12 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass13 : (((elemsCL QA u33QACodes).drop (13 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass14 : (((elemsCL QA u33QACodes).drop (14 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass15 : (((elemsCL QA u33QACodes).drop (15 * 756)).take 756).all pPass = true := by
  decide +kernel

theorem kPass : passO inP (elemsC QA) (elemsC QS) gS csO csI tO tI = true := by
  rw [inP_eq, elemsC_eq_elemsCL u33QA_strong, elemsC_eq_elemsCL u33QS_strong]
  exact CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ pPass 756 16 kPassLen fun j hj =>
    match j, hj with
    | 0, _ => kPass0
    | 1, _ => kPass1
    | 2, _ => kPass2
    | 3, _ => kPass3
    | 4, _ => kPass4
    | 5, _ => kPass5
    | 6, _ => kPass6
    | 7, _ => kPass7
    | 8, _ => kPass8
    | 9, _ => kPass9
    | 10, _ => kPass10
    | 11, _ => kPass11
    | 12, _ => kPass12
    | 13, _ => kPass13
    | 14, _ => kPass14
    | 15, _ => kPass15
    | k + 16, h => absurd h (by omega)

theorem kSubO : sub3C csO tO = true := by decide +kernel

theorem kSubI : sub3C csI tI = true := by decide +kernel

theorem kBang : bangC tO bl bc₁ bc₂ = true := by decide +kernel

theorem kWord : wordWC (cOf s0) wa wb = true := by decide +kernel

theorem kConj4 : conj4KC (elemsC QS) refs ks = true := by decide +kernel

theorem kE3 : inP (cOf t0) = true ∧ powOneC (cOf t0) 2 = true ∧ decide (cOf t0 = 1) = false ∧
    powOneC e3 3 = true ∧ decide (e3 = 1) = false ∧ eq22C e3 (cOf t0) (cOf t0) e3 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem kOut : inP tO = false ∧ inP tI = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.U33R.KOut

end
