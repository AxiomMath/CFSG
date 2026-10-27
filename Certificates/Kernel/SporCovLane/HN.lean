module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.LaneKit
public import Certificates.Data.Kernel.SporCov.PcCl
public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel

#kc_repo #kc_json_gz CFSG.KD.SporCovLane.HN.D "Certificates/Kernel/SporCovLane/data/hn3.json.gz"
  10267 1878844991063739519
  (Ws : List (List Nat))
  (HA : List (List Nat)) (RlA : List (List Nat)) (TA : List Nat) (MA : List (List Nat))
  (YA : List (List Nat)) (HcA : List (List Nat)) (YcA : List (List Nat)) (KA : List Nat)
  (CA : List (List Nat)) (RA : List (List Nat))
  (HB : List (List Nat)) (RlB : List (List Nat)) (TB : List Nat) (MB : List (List Nat))
  (YB : List (List Nat)) (HcB : List (List Nat)) (YcB : List (List Nat)) (KB : List Nat)
  (CB : List (List Nat)) (RB : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovLane.HN

open CFSG.KC.SporCov CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat :=
  mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

@[expose] noncomputable def chk (mw : List Nat → Nat) : Bool :=
  pccOK (eqM mw) letT 3 4 4 2 2 D.HA D.RlA D.TA D.MA D.YA D.HcA D.YcA D.CA D.RA D.KA &&
    pccOK (eqM mw) letT 3 3 4 2 2 D.HB D.RlB D.TB D.MB D.YB D.HcB D.YcB D.CB D.RB D.KB &&
    !Nat.beq (Nat.mod (trR 13 1729 133 (mw D.TA)) 5) (Nat.mod (trR 13 1729 133 (mw D.TB)) 5)

namespace Ck

theorem ok : kitLn mul CFSG.KD.FamHNSeed.ONE (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 1)
    (CFSG.KD.FamHNSeed.RW 2) (mul (CFSG.KD.FamHNSeed.RW 2) (CFSG.KD.FamHNSeed.RW 2)) D.Ws chk =
      true := by
  quickRfl

end Ck

end CFSG.KD.SporCovLane.HN

end
