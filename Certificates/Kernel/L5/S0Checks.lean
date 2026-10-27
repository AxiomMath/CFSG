module

public import Certificates.Data.Kernel.L5.S0C

public section

namespace CFSG.KD.L5.S0Checks

open CFSG.KD.L5 CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5

set_option maxRecDepth 100000

theorem all_ok : (tabC.all (fun e => decide (wval gC e.2 = e.1) && decide (e.1 ∈ SC)) &&
    SC.all (fun s => tabC.any fun e => decide (e.1 = s)) &&
    gC.all (fun g => decide (g ∈ SC)) &&
    decide (tabC.map Prod.fst).Nodup &&
    [t1, t2, t3].all (fun t => decide (t.1 ∈ tabC.map Prod.snd) &&
      decide (t.2.1 ∈ tabC.map Prod.snd) && decide (t.2.2 ∈ tabC.map Prod.snd) &&
      holdsC gC t) &&
    AC.all (fun u₁ => BC.all fun u₂ => !holdsC (fixC ++ [u₁, u₂]) t3) &&
    !AC.all (fun u₁ => BC.all fun u₂ => !holdsC (fixC ++ [u₁, u₂]) t1)) = true := by
  decide +kernel

theorem hA : tabC.all (fun e => decide (wval gC e.2 = e.1) && decide (e.1 ∈ SC)) = true := by
  have h := all_ok
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

theorem hB : SC.all (fun s => tabC.any fun e => decide (e.1 = s)) = true := by
  have h := all_ok
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem hC : gC.all (fun g => decide (g ∈ SC)) = true := by
  have h := all_ok
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem hN : (tabC.map Prod.fst).Nodup := by
  have h := all_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem hW : [t1, t2, t3].all (fun t => decide (t.1 ∈ tabC.map Prod.snd) &&
    decide (t.2.1 ∈ tabC.map Prod.snd) && decide (t.2.2 ∈ tabC.map Prod.snd) &&
    holdsC gC t) = true := by
  have h := all_ok
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem hD : AC.all (fun u₁ => BC.all fun u₂ => !holdsC (fixC ++ [u₁, u₂]) t3) = true := by
  have h := all_ok
  simp only [Bool.and_eq_true] at h
  exact h.1.2

end CFSG.KD.L5.S0Checks

end
