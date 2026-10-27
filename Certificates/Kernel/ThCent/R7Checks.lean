module

public import Certificates.Kernel.ThCent.LDefs
public import Certificates.Data.Kernel.ThCent.Rank
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace CFSG.KD.ThCent.L

open CFSG.KC.Th CFSG.KC.ThCent

@[expose] noncomputable def r7 (k : Nat) : Bool :=
  chunkOK (fun e => rank7OK ThS.c ThS.rm ThS.ONE V7 (V7 25) e.1) L7.E (k * 49) 49

@[expose] noncomputable def ord4 : Bool :=
  ord4OK ThS.c ThS.rm ThS.ONE V7 (L7.E.getD 153 ([], [], 0)).1

theorem ord4_ok : ord4 = true := by quickRfl

end CFSG.KD.ThCent.L

end
