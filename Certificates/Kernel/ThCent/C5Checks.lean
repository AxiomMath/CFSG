module

public import Certificates.Kernel.ThCent.LDefs
public import Certificates.Data.Kernel.ThCent.Cent5
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace CFSG.KD.ThCent.L

open CFSG.KC.Th CFSG.KC.ThCent

@[expose] def letters5 : List Nat := [19, 114, 99, 115]

@[expose] def lett5 : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(19, 114, 2, 4, 4, 2, 2, 4), (114, 19, 2, 1, 2, 3, 2, 1), (99, 115, 1, 1, 4, 3, 4, 2),
    (115, 99, 4, 4, 2, 2, 1, 2)]

@[expose] noncomputable def cn5 (k : Nat) : Bool :=
  chunkOK (fun e => cent5OK ThS.c ThS.rm ThS.ONE V5 (V5 94) (V5 105) C5 e.1) L5.E (k * 50) 50

@[expose] noncomputable def let5 (t : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Bool :=
  strictF C5 fun C => letterOK ThS.c ThS.rm ThS.ONE (V5 t.1) (V5 t.2.1) (V5 94) (V5 105) C
    t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2

theorem letters5_ok : (L5.E.all fun e => e.1.all fun r => letters5.elem r) = true := by
  decide +kernel

theorem lett5_ok : lett5.all let5 = true := by quickRfl

end CFSG.KD.ThCent.L

end
