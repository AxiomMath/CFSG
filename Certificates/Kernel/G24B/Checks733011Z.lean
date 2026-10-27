module

public import Certificates.Kernel.G24B.Checks733011
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_repo #kc_json_gz CFSG.KD.G24B "Certificates/Kernel/G24B/data/z.json.gz" 2085 15149280164801978724
  (zc : List Nat)

namespace CFSG.KD.G24B

open CFSG.KC.Misc.G24 CFSG.KC.F2BfsRec CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Quasithin.St84.G24Ident

@[expose] noncomputable def zcStepK (s j : Nat) : Bool :=
  strictB (sortedAt 28 12 6 10 EQ2.CF s) fun X =>
    bIf(commK X (blowW k2), andB (Nat.blt j 1024) (andB (Nat.beq (Nat.mod j 64) 0)
      (Nat.beq X (pcK GQ2 j))), true)

@[expose] noncomputable def zcGoK (zc : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun j _ ih s => andB (zcStepK s j) (ih (Nat.succ s))) zc

@[expose] noncomputable def zcK (zc : List Nat) : Bool :=
  andB (Nat.beq (List.length zc) 1024) (zcGoK zc 0)

theorem ch733011_zc : zcK zc = true := by quickRfl

theorem ch733011_negZc : (!zcK (zc.map Nat.succ)) = true := by quickRfl

end CFSG.KD.G24B

end
