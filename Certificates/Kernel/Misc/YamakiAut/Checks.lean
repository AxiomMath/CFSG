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

@[expose] def wl0 : List Nat := [5, 8, 6, 7, 3, 10, 11, 2, 0, 1, 9, 4]

@[expose] def wl1 : List Nat := [5, 4, 7, 3, 2, 6, 11, 10, 1, 9, 8, 0]

@[expose] def wOne : Nat := 205163983024656

@[expose] def wPi : Nat := 92574005762166

@[expose] noncomputable def ch550851C (q : Nat) : Bool := autChunk RH RW wl0 wl1 wOne 23040 512 q

theorem ch550851i : invPosK RH 23040 [(31, 0), (165, 1)] = true := by quickRfl

theorem ch550851u : (Nat.beq (recX RH 14 22990) (RH 5) && Nat.beq (RW 22990) wPi) = true := by
  quickRfl

theorem ch550851nA : (!autChunk RH RW wl1 wl0 wOne 23040 512 0) = true := by quickRfl

theorem ch550851nB : (!autChunk RH (fun t => RW (Nat.add t 1)) wl0 wl1 wOne 23040 512 7) = true := by
  quickRfl

theorem ch550851nC : (!autChunk RH RW wl0 wl1 wPi 23040 512 0) = true := by quickRfl

theorem ch550851nD : (!invPosK RH 23040 [(31, 1), (165, 1)]) = true := by quickRfl

theorem ch550851nE : (!(Nat.beq (RW 22990) wOne)) = true := by quickRfl

end CFSG.KD.YamakiAut

#kc_slices CFSG.KD.YamakiAut.ch550851K CFSG.KD.YamakiAut.ch550851C 45

end
