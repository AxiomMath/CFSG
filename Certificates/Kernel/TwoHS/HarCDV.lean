module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.TwoHS.HarCD
import Certificates.Kernel.TwoHS.HarCD
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

namespace CFSG.KD.TwoHS.HarCDV

meta def fnv (t : Array Nat) : Nat :=
  t.foldl (fun h x => ((h ^^^ x) * 1099511628211) % 18446744073709551616) 14695981039346656037

meta def hvU : Array (Array Nat) := CFSG.KD.TwoHS.HarCD.recU.map fun t => #[fnv t]

end CFSG.KD.TwoHS.HarCDV

public section

#kc_items CFSG.KD.TwoHS.TEV include_bytes "data/HarCDV.TEV.items" 12287 10870747312867030174

end
