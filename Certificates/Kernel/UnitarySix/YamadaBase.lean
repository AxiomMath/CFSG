
module

public import Certificates.Kernel.UnitarySix.LettersBase
public import CFSG.Certificates.Kernel.U6Sound3000
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeDataBase
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

@[expose] public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix CFSG.EvenSmallLie.UnitarySix.Yamada

@[expose] noncomputable def aWK : List (List Nat) :=
  [[0], [22], [90], [32, 90, 14, 91, 33], [68], [66, 90, 40, 91, 67], [62, 90, 36, 91, 63],
    [14, 90, 70, 40, 90, 2, 91, 41, 71, 91, 15], [76, 90, 48, 91, 77]]

@[expose] noncomputable def kWK : List (List Nat) :=
  [[6, 20, 40, 66], [30, 90, 2, 91, 31, 12, 90, 2, 91, 13], [30, 90, 2, 91, 31, 90, 34, 91]]

@[expose] noncomputable def oWK : List (List Nat) :=
  [[], [0], [1], [2, 0], [4, 0], [0, 2, 0], [4, 2, 0], [1, 2, 0], [0, 4, 0], [1, 4, 0], [2, 0, 2, 0],
    [4, 0, 2, 0], [0, 4, 2, 0], [1, 4, 2, 0], [2, 0, 4, 0], [4, 0, 4, 0], [4, 2, 0, 2, 0],
    [0, 4, 0, 2, 0], [1, 4, 0, 2, 0], [4, 0, 4, 2, 0], [4, 1, 4, 0, 2, 0]]

@[expose] noncomputable def sWK : List (List Nat) :=
  [[], [], [1, 2, 1, 2, 1, 2, 0, 2, 0, 2], [2], [4], [2, 1, 2, 0, 2, 1, 2, 0], [2, 4],
    [1, 2, 1, 2, 1, 2, 0, 2, 0], [4, 1, 4, 0, 4, 1, 4, 0], [1, 4, 1, 4, 1, 4, 0, 4, 0],
    [1, 2, 0, 2, 1, 2, 0], [2, 4, 1, 2, 0, 2, 1, 2, 0], [2, 1, 4, 0, 2, 1, 4, 0],
    [1, 2, 4, 1, 2, 1, 4, 0, 2, 0], [2, 4, 1, 4, 0, 4, 1, 4, 0], [1, 4, 0, 4, 1, 4, 0],
    [4, 1, 2, 0, 2, 1, 2, 0], [2, 1, 4, 0, 4, 1, 4, 0], [1, 4, 0, 2, 1, 4, 0], [1, 2, 0, 4, 1, 2, 0],
    [2, 1, 2, 0, 4, 1, 2, 0]]

theorem aW_eq : aWords = aWK.map (List.map decZ) := rfl
theorem kW_eq : kWords = kWK.map (List.map decZ) := rfl
theorem oW_eq : orbitWords = oWK.map (List.map decZ) := rfl
theorem sW_eq : stabWords = sWK.map (List.map decZ) := rfl

theorem k3000 : check3000 U.LT aWK kWK oWK sWK = true := by quickRfl

end CertificateChecks.KernelU6

end
