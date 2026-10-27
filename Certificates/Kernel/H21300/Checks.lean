module

public import Certificates.Data.Kernel.H21300
meta import Certificates.Data.Kernel.H21300
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.SporSch.Mathieu.Gen

public section

namespace CFSG.KD.H21300.Gen

open CFSG.KD.H21300

meta def uSrc : Array Nat := (LUs.map pack).toArray

meta def tSrc : Array Nat := (LTs.map pack).toArray

meta def firstW (c d : Nat) : Nat :=
  ((List.range 42).find? fun i =>
    cnt (evalL (decode c) (decode d) (CFSG.Holt.SmallGroups.s7Words.getD i [])) == 2).getD 63

meta def hintOf (c : Nat) : Nat :=
  (LTs.map pack).foldr (fun d acc => firstW c d + 64 * acc) 0

meta def hSrc : Array Nat := (LUs.map fun a => hintOf (pack a)).toArray

meta def hBad : Array Nat :=
  (LUs.map fun a => hintOf (pack a) - hintOf (pack a) % 64 + 63).toArray

end CFSG.KD.H21300.Gen

#kss_list CFSG.KD.H21300.UC CFSG.KD.H21300.Gen.uSrc

#kss_list CFSG.KD.H21300.TC CFSG.KD.H21300.Gen.tSrc

#kss_list CFSG.KD.H21300.HC CFSG.KD.H21300.Gen.hSrc

#kss_list CFSG.KD.H21300.HB CFSG.KD.H21300.Gen.hBad

namespace CFSG.KD.H21300

theorem covU : covB LUs UC = true := by decide +kernel

theorem covT : covB LTs TC = true := by decide +kernel

theorem chk_ok : chkH TC UC HC = true := by decide +kernel

theorem neg21300_cov : (!covB LUs TC) = true := by decide +kernel

theorem neg21300_hint : (!chkH TC UC HB) = true := by decide +kernel

end CFSG.KD.H21300

end
