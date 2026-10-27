module

public import CFSG.Certificates.Kernel.Misc.G22WSound
public import Certificates.Kernel.Misc.G22W.Checks

public section

namespace CFSG.KD.G22W

open CFSG.Quasithin.H13.KGCert CFSG.KC.Mat8P

theorem g22w_gens : unpackM (REC 0) = gAc ++ [64, 128] ∧ unpackM (REC 1) = gBc ++ [64, 128] := by
  decide +kernel

theorem cert7102_ok : g22Elems.length = 12096 ∧ oneC ∈ g22Elems ∧ g22ValidCheck = true ∧
    g22ClosedCheck = true ∧ g22StabCheck = true ∧ g22NodupCheck = true :=
  CFSG.KC.G22W.cert7102_of (hi := 189) (hiT := 189) (by norm_num) (by norm_num) (by norm_num)
    g22w_gens.1 g22w_gens.2 g22w_search_ok g22w_prod_ok g22w_sort_ok g22w_stab_ok

end CFSG.KD.G22W

end
