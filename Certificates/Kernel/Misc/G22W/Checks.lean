module

public import Certificates.Data.Kernel.Misc.G22W
public import Certificates.Kernel.Misc.G22W.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G22W

theorem g22w_search_ok : searchK REC 12096 = true := by quickRfl

theorem g22w_prod_ok : prodK REC 12096 189 = true := by quickRfl

theorem g22w_sort_ok : sortX REC 12096 189 = true := by quickRfl

theorem g22w_stab_ok : stabK REC 12098 12096 189 = true := by quickRfl

end CFSG.KD.G22W

end
