
module

public import Certificates.Kernel.UnitarySix.LettersBase
public import CFSG.Certificates.Kernel.U6Sound3010S
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

@[expose] public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

noncomputable def aWN : List (List Nat) :=
  [[0], [22], [90], [32, 90, 14, 91, 33], [68], [66, 90, 40, 91, 67], [62, 90, 36, 91, 63],
    [14, 90, 70, 40, 90, 2, 91, 41, 71, 91, 15], [76, 90, 48, 91, 77]]

noncomputable def kWN : List (List Nat) :=
  [[6, 20, 40, 66], [30, 90, 2, 91, 31, 12, 90, 2, 91, 13], [30, 90, 2, 91, 31, 90, 34, 91]]

noncomputable def tWN : List (List Nat) :=
  [[30, 90, 2, 91, 31, 12, 90, 2, 91, 13], [30, 90, 2, 91, 31, 90, 34, 91],
    [62, 90, 52, 91, 63, 72, 90, 36, 91, 73], [62, 90, 52, 91, 63, 82, 90, 44, 91, 83]]

noncomputable def TWN : List (List Nat) := [[2], [4], [0, 2, 1], [0, 4, 1]]

noncomputable def MS : Nat := nat_lit 399156334087647545403135851969738099102369672365729175408256207001216732809027519691162597861368760410222882352488961797538898013144539530154972747785922838729848984182786

theorem aWN_eq : aWords = aWN.map (List.map decZ) := rfl
theorem kWN_eq : kWords = kWN.map (List.map decZ) := rfl
theorem tWN_eq : tWords = tWN.map (List.map decZ) := rfl

theorem k3010S : check3010S U.LT aWN kWN tWN MS TWN = true := by quickRfl

theorem k3010O : check3010O U.LT aWN kWN MS = true := by quickRfl

end CertificateChecks.KernelU6

end
