module

public import CFSG.Certificates.Kernel.Misc.G22CSound
public import Certificates.Kernel.Misc.G22W.Final
public import Certificates.Kernel.Misc.G22C.Checks

public section

namespace CFSG.KD.G22C

open CFSG.Quasithin.H13.KGCert CFSG.KC.Mat8P CFSG.KD.G22W

theorem g22c_facts : g22Elems = (List.range 12096).reverse.map (CFSG.KC.G22W.E REC) ∧
    ∀ t < 12096, goodK (numX REC t) = true := by
  have hfac := CFSG.KC.G22W.prod_facts g22w_prod_ok (by norm_num) g22w_gens.1 g22w_gens.2
  have hinj := CFSG.KC.G22W.E_inj g22w_prod_ok (by norm_num) g22w_sort_ok (by norm_num)
  exact ⟨(CFSG.KC.G22W.g22Elems_eq g22w_search_ok (by norm_num) (fun t ht => (hfac t ht).2)
    hinj).2, fun t ht => (hfac t ht).1⟩

theorem g22c_reps : unpackM (repT REC CR 12096 false) = t0C ++ [64, 128] ∧
    unpackM (repT REC CR 12096 true) = t1C ++ [64, 128] := by
  decide +kernel

theorem cert7129_ok : g22ConjCheck = true :=
  CFSG.KC.G22C.conj_check g22c_facts.1 g22c_facts.2 g22c_reps.1 g22c_reps.2 g22c_conj_ok
    (by norm_num)

end CFSG.KD.G22C

end
