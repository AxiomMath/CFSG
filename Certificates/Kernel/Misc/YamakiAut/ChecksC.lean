module

public import Certificates.Data.Kernel.Misc.YamakiAutC
public import Certificates.Kernel.Misc.YamakiRep.Rec
public import Certificates.Kernel.Misc.YamakiAut.RecC
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiAutC

open CFSG.KD.YamakiRep CFSG.KD.BfsK
open CFSG.KD.Sp62 (ONE)

@[expose] def cr0 : Nat := 42718597939

@[expose] def cr1 : Nat := 50374512136

@[expose] def pc1 : List Nat :=
  [42718597939, 10841982323, 10841982323, 42718597939, 42137404184, 43211111896, 43211111896,
    42137404184, 21243715123, 12989491699, 60233917683, 4802405209, 42718597939, 41321024493,
    19846366957, 52046966361]

@[expose] def pc2 : List Nat :=
  [22569943731, 20427730483, 41902482227, 35454799795, 59082287623, 20427730483, 41902482227,
    3247924999, 35454799795, 19353990003, 67465902195, 35950215057, 14857585843, 44528578725,
    3726546725, 12327983121]

@[expose] def ts2 : List (List Nat) :=
  [[0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1], [0, 0, 1, 1, 1, 0, 0, 1, 1, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    [0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,
     0, 0, 1]]

@[expose] noncomputable def ch550712c1 (q : Nat) : Bool := c1Chunk RX HC1 1536 cr0 cr1 512 q

@[expose] noncomputable def ch550712c2 (q : Nat) : Bool :=
  c2Chunk RX HC2 (fun k => pc1.getD k 0) (fun k => pc2.getD k 0) ts2 1536 cr0 cr1 512 q

theorem ch550712c1n : (!c1Chunk RX (fun i => HC1 (Nat.add i 1)) 1536 cr0 cr1 512 0) = true := by
  quickRfl

theorem ch550712c1m : (!c1Chunk RX HC1 1536 cr1 cr0 512 0) = true := by quickRfl

theorem ch550712c2n :
    (!c2Chunk RX (fun i => HC2 (Nat.add i 1)) (fun k => pc1.getD k 0) (fun k => pc2.getD k 0) ts2
      1536 cr0 cr1 512 0) = true := by quickRfl

theorem ch550712c2m :
    (!c2Chunk RX HC2 (fun k => pc2.getD k 0) (fun k => pc1.getD k 0) ts2 1536 cr0 cr1 512 0) =
      true := by quickRfl

theorem ch550712c2t :
    (!c2Chunk RX (fun _ => 0) (fun k => pc1.getD k 0) (fun k => pc2.getD k 0) ts2 1536 cr0 cr1
      512 0) = true := by quickRfl

end CFSG.KD.YamakiAutC

#kc_slices CFSG.KD.YamakiAutC.ch550712c1K CFSG.KD.YamakiAutC.ch550712c1 3
#kc_slices CFSG.KD.YamakiAutC.ch550712c2K CFSG.KD.YamakiAutC.ch550712c2 3

end
