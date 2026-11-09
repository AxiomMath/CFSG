module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8Inputs
public import Certificates.Data.Kernel.PermCent.SemiReg

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5128

open CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum

@[expose] def sz8R : List Nat := [0]

@[expose] def sz8Rho : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def sz8W : List (List Bool) :=
  [[], [true, false, true, false, true, true, true, false, true], [false, true, true, false], [true, false, true, false], [false, true, false, true, true, true, false, true, true, false], [false, true, true, false, true, true, true], [false, true, false, true, true, true, false, true, true], [false, true, false, true, false, true, true, false, true, true], [false, true, false, true, true], [true, true, false, true, true], [true, true, true], [true, false, true, true], [false, true, false, true], [false, true], [false, true, false], [true, true, false], [false, true, true, false, true, true, false, true, false], [false, true, false, true, true, true], [true, true, false, true, true, true], [false, true, true, false, true, true], [false, true, true, true, false], [false, true, false, true, false, true, true, true, false, true], [false, true, true], [true, false, true], [false, true, true, true, false, true, false, true], [true, true, false, true, true, true, false, true, true, false], [false, true, false, true, true, false, true, true, false, true, false], [true, false, true, false, true, true, true], [true, true, false, true, true, false], [true, false, true, false, true], [false, true, true, true, false, true, true, false], [false, true, false, true, true, true, false, true], [true, true, false, true, true, true, false, true], [true, true, true, false, true, true, false], [true], [true, false, true, false, true, true, false, true, true], [true, false], [false, true, false, true, true, false, true, true], [true, true, false, true, true, true, false, true, true], [false, true, true, false, true, true, true, false, true], [true, false, true, true, false, true, true], [false, true, true, true, false, true], [false, true, true, true, false, true, true], [true, true, false, true, false, true], [true, true, true, false], [true, true, false, true], [true, false, true, true, true, false, true, true], [true, true, true, false, true], [false, true, false, true, false, true, true, true], [false, true, true, false, true, false], [true, false, true, true, true, false, true, true, false], [true, false, true, true, false], [true, true, true, false, true, true, true, false, true], [true, false, true, true, true], [true, true, true, false, true, true], [false], [true, true, false, true, true, false, true, false], [false, true, false, true, true, false, true, false], [true, true, true, false, true, false, true], [true, true, false, true, false], [false, true, true, true], [true, false, true, true, true, false, true], [true, false, true, true, false, true, false], [true, true], [true, false, true, true, false, true, true, false, true, false]]

@[expose] def sz8Wit : List (Nat × Bool) :=
  [(0, false), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (3, false), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]

set_option maxRecDepth 100000 in
theorem sz8Semi : SemiReg.semiregChk 65 (img 65 (cOf pa).1) (img 65 (cOf pb).1) sz8R sz8Rho sz8W
    sz8Wit = true := by
  decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf pa) (cOf pb) = true :=
  SemiReg.centTrivC_of_semireg _ _ _ sz8Semi

theorem kCent_neg : centTrivC (elemsC QA) 1 1 = false := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5128
