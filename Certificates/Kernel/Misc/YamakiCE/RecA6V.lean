module

public meta import Lean
meta import Certificates.Data.Sp62RecCR1CE
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Tactic.NormNum.Ineq

namespace CFSG.KD.YamakiA6.GenV

open CFSG.KD.YamakiRep.Gen CFSG.ClassicalInvolution.Sp62Rec

meta def posVE : List Nat := Id.run do
  let (ee, _, _, _) := bfsM (e0Words.map wordM).toArray 11520
  let (ev, _, _, _) := bfsM (v0Idx.map fun i => gM[i]!).toArray 32
  let idx : Std.HashMap Nat Nat := (List.range ee.size).foldl (fun m i => m.insert ee[i]! i) {}
  return ev.toList.map fun x => (idx.get? x).getD 65535

end CFSG.KD.YamakiA6.GenV

#kss_ntree CFSG.KD.YamakiA6.PVE CFSG.KD.YamakiA6.GenV.posVE
