module

public import Certificates.Data.Kernel.Misc.YamakiAut
public import Certificates.Kernel.Misc.YamakiRep.Rec
public import Certificates.Kernel.Misc.YamakiAut.Rec
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiAut

open CFSG.KD.YamakiRep CFSG.KD.BfsK

@[expose] def ql0 : List Nat := [8, 2, 12, 4, 3, 0, 6, 1, 9, 5, 11, 10, 7, 13]

@[expose] def ql1 : List Nat := [2, 10, 1, 12, 7, 13, 4, 9, 3, 8, 5, 0, 6, 11]

@[expose] def qOne : Nat := 62129658859368976

@[expose] noncomputable def ch550831C (q : Nat) : Bool := autChunk RN RQ ql0 ql1 qOne 10752 512 q

theorem ch550831i : invPosK RN 10752 [(7, 0), (114, 1)] = true := by quickRfl

theorem ch550831nA : (!autChunk RN RQ ql1 ql0 qOne 10752 512 0) = true := by quickRfl

theorem ch550831nB : (!autChunk RN (fun t => RQ (Nat.add t 1)) ql0 ql1 qOne 10752 512 5) = true := by
  quickRfl

theorem ch550831nC : (!autChunk RN RQ ql0 ql1 (Nat.add qOne 1) 10752 512 0) = true := by quickRfl

theorem ch550831nD : (!invPosK RN 10752 [(7, 0), (115, 1)]) = true := by quickRfl

end CFSG.KD.YamakiAut

#kc_slices CFSG.KD.YamakiAut.ch550831K CFSG.KD.YamakiAut.ch550831C 21

end
