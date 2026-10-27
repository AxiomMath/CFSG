module

public import Certificates.Data.Kernel.Misc.G23Emb
public import Certificates.Data.G23Emb
public import Certificates.Kernel.Misc.G23Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G23Emb

open CFSG.KC.Misc.G24 CFSG.KC.Misc.G23 CFSG.KC.Misc.G23Emb CFSG.KD.Misc.G23
open CFSG.LieType.Multipliers.G23 CFSG.CGT.PushingUpLit.CGT6.EmbModule

@[expose] noncomputable def encC (w : List (Fin 2 × Bool)) : List Nat :=
  w.map fun l => 2 * l.1.val + if l.2 then 1 else 0

@[expose] noncomputable def BiK : Nat := mulF2 54 Bb Bb

@[expose] noncomputable def RK : List Nat :=
  (List.finRange 4).map fun j => wordM Ab Bb BiK (encC (genWord j))

@[expose] noncomputable def UK : Nat := prodK RK (uW.map Fin.val)

@[expose] noncomputable def VK : Nat := prodK RK (vW.map Fin.val)

@[expose] noncomputable def A1K : Nat := prodK RK (a1W.map Fin.val)

@[expose] noncomputable def A2K : Nat := prodK RK (a2W.map Fin.val)

theorem check : embK UK VK A1K A2K = true := by quickRfl

end CFSG.KD.Misc.G23Emb

end
