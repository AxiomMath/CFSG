module

public meta import Lean
meta import Certificates.Data.YamakiTables
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.YamakiNA.GenH

open CFSG.KD.YamakiRep.Gen CFSG.ClassicalInvolution.Solomon73.Yamaki

meta def posHX : List Nat := Id.run do
  let (eh, _, _, _) := bfsM (hWords.map wordM).toArray 23040
  let (ex, _, _, _) := bfsM (gWords.map wordM).toArray 1536
  let idx : Std.HashMap Nat Nat := (List.range ex.size).foldl (fun m i => m.insert ex[i]! i) {}
  return eh.toList.map fun x => (idx.get? x).getD 65535

end CFSG.KD.YamakiNA.GenH

#kss_ntree CFSG.KD.YamakiNA.PHX CFSG.KD.YamakiNA.GenH.posHX
