module

public import Certificates.Kernel.U34Orb.D

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.U34Orb

open Certificates.U34Orb

theorem iLet : lettersOK iG = true := by decide +kernel

theorem iTr1 : treeOK iG iP iT1 65 = true := by decide +kernel

theorem iSch : schOK iG iP iS = true := by decide +kernel

theorem iTr2 : treeOK (iS.map (·.1)) iQ iT2 64 = true := by decide +kernel

theorem iW15 : wOK iG iP iQ iW = true := by decide +kernel

theorem iOK : orbOK iG iP iT1 iS iQ iT2 iW = true := by
  rw [orbOK, iLet, iTr1, iSch, iTr2, iW15]
  rfl

theorem oLet : lettersOK oG = true := by decide +kernel

theorem oTr1 : treeOK oG oP oT1 65 = true := by decide +kernel

theorem oSch : schOK oG oP oS = true := by decide +kernel

theorem oTr2 : treeOK (oS.map (·.1)) oQ oT2 64 = true := by decide +kernel

theorem oW15 : wOK oG oP oQ oW = true := by decide +kernel

theorem oOK : orbOK oG oP oT1 oS oQ oT2 oW = true := by
  rw [orbOK, oLet, oTr1, oSch, oTr2, oW15]
  rfl

end CFSG.KD.U34Orb
