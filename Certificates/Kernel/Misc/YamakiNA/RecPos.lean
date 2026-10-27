module

public meta import Lean
meta import Certificates.Data.YamakiTables
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.YamakiNA.Gen

open CFSG.KD.YamakiRep.Gen CFSG.ClassicalInvolution.Solomon73.Yamaki

meta def posNX : List Nat := Id.run do
  let (en, _, _, _) := bfsM (nWords.map wordM).toArray 10752
  let (ex, _, _, _) := bfsM (gWords.map wordM).toArray 1536
  let idx : Std.HashMap Nat Nat := (List.range ex.size).foldl (fun m i => m.insert ex[i]! i) {}
  return en.toList.map fun x => (idx.get? x).getD 65535

end CFSG.KD.YamakiNA.Gen

#kss_ntree CFSG.KD.YamakiNA.PNX CFSG.KD.YamakiNA.Gen.posNX
