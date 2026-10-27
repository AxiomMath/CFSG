module

public import CFSG.Certificates.Kernel.E6Syl3CGlue
public import Certificates.Kernel.E6Syl3.Checks
public import Certificates.Kernel.E6Syl3.ChecksP
public import Certificates.Kernel.E6Syl3.ChecksC

public section

namespace CFSG.KD.E6Syl3

open CFSG.KC.E6Syl3

theorem e6CaseITable :
    CFSG.LieType.SeitzGeneration.ExcWideThree.E6CaseITable :=
  e6CaseITable_of_checks (gw := gw) (wd := wd) (lt := lt) (kw := kw) (cw := cw) (o3 := o3)
    (by rw [ch214105_tups]; exact ch214105_q) (by rw [ch214105_tups]; exact ch214107_wd)
    (by rw [ch214105_tups]; exact ch214107_lt) (by rw [ch214105_tups]; exact ch214105_kinds)
    ch214107_o3 ch214106_gen (by rw [ch214105_tups]; exact ch214106_elems)
    (by rw [ch214105_tups]; exact ch214106_pairs)

end CFSG.KD.E6Syl3
