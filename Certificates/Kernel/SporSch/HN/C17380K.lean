module

public import Certificates.Kernel.SporSch.HN.C13609Data
public import Certificates.Data.Kernel.SporSch.ConjKey
public import Certificates.Data.Kernel.SporSch.RelTab
public import CFSG.Certificates.Kernel.Local.HN.Lib
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HN17380

open CFSG.KC.ConjKey CFSG.KC.RelTab

local notation "mm" => CFSG.KC.LL.HN.mm
local notation "G3" => CFSG.KD.HNPt2109.G3F
local notation "ONE" => CFSG.KD.OrdHN.ONE

@[expose] noncomputable def Z : Nat := CFSG.KD.HNPt2109.S2
@[expose] noncomputable def Z2 : Nat := mm Z Z
@[expose] noncomputable def X3 : Nat := mm (mm (G3 1) (G3 0)) (G3 0)
@[expose] noncomputable def X4 : Nat := mm (mm (mm (mm (G3 6) (G3 1)) (G3 6)) (G3 4)) (G3 0)
@[expose] noncomputable def XS (i : Nat) : Nat := [G3 3, G3 5, X3, X4].getD i 0
@[expose] noncomputable def PW (j : Nat) : Nat :=
  [Z, Z2, G3 3, mm (G3 3) (G3 3), G3 5, mm (G3 5) (G3 5), X3, mm X3 X3, X4, mm X4 X4].getD j 0
@[expose] noncomputable def A : Nat := mm (mm (G3 6) (G3 3)) (G3 0)
@[expose] noncomputable def A2 : Nat := mm A A
@[expose] noncomputable def B : Nat :=
  prodL mm ONE G3 [3, 2, 6, 6, 1, 0, 6, 6, 0, 0]

@[expose] def nRows : List (Nat × Nat × List Nat) :=
  [(0, 0, [0, 2, 7]), (0, 1, [4]), (0, 2, [6]), (0, 3, [1, 5, 7, 8]),
   (1, 0, [2, 7]), (1, 1, [4]), (1, 2, [6]), (1, 3, [0, 5, 7, 8]),
   (2, 0, [1, 2, 7]), (2, 1, [4]), (2, 2, [6]), (2, 3, [5, 7, 8]),
   (4, 0, [3]), (4, 1, [5]), (4, 2, [7]), (4, 3, [0, 9]),
   (6, 0, [1, 5, 7]), (6, 1, [0, 9]), (6, 2, [2, 6, 8]), (6, 3, [2, 4, 6])]

theorem ch17380_r1 : eqK (mm (PW 3) (G3 3)) ONE = true ∧ eqK (mm (PW 5) (G3 5)) ONE = true ∧
    eqK (mm (PW 7) X3) ONE = true ∧ eqK (mm (PW 9) X4) ONE = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem ch17380_r2 : eqK (mm (G3 3) X3) (mm Z (mm X3 (G3 3))) = true ∧
    eqK (mm (G3 3) X4) (mm Z (mm X4 (G3 3))) = true ∧
    eqK (mm (G3 5) X4) (mm Z (mm X4 (G3 5))) = true ∧
    eqK (mm X3 X4) (mm Z2 (mm X4 X3)) = true ∧
    eqK (mm (G3 3) (G3 5)) (mm (G3 5) (G3 3)) = true ∧
    eqK (mm (G3 5) X3) (mm X3 (G3 5)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem ch17380_z : eqK (mm Z2 Z) ONE = true ∧ Bool.not (eqK (vmHN 1 Z) 1) = true := by
  refine ⟨?_, ?_⟩ <;> quickRfl

theorem ch17380_n : relTab mm ONE G3 XS PW nRows = true := by quickRfl

theorem ch17380_q : eqK (mm A2 A2) ONE = true ∧ Bool.not (eqK (vmHN 1 A2) 1) = true ∧
    eqK (mm B B) A2 = true ∧ eqK (mm (mm A B) A) B = true ∧
    Bool.not (eqK (vmHN (vmHN 1 A2) (G3 3)) (vmHN (vmHN 1 (G3 3)) A2)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem ch17380_w : eqK (mm (mm (G3 0) (G3 0)) (G3 0)) ONE = true := by quickRfl

theorem ch17380_y : Bool.not (eqK (vmHN (vmHN 1 CFSG.KD.HN13609.Y) (G3 3))
    (vmHN (vmHN 1 (G3 3)) CFSG.KD.HN13609.Y)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HN17380

end
