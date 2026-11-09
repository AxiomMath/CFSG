module

public import Certificates.Data.Kernel.L5.S0C
public import Certificates.Data.Kernel.L5.ClosureFast

public section

namespace CFSG.KD.L5.S0Checks

open CFSG.KD.L5 CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5

set_option maxRecDepth 100000

@[expose] noncomputable def SCK : List (CV 16) :=
  ((Fast.closureStepK (fun a : CV 16 => a.1) (sh1Gens.map cOf))^[12] [1]).filter ovC

theorem SC_eq : SC = SCK := by
  rw [SC, SCK, Fast.closureList_eq_K Subtype.val_injective]

theorem AC_eq : AC = SCK.filter fun u => holdsC (fixC ++ [u, 1]) t1 := by
  rw [AC, SC_eq]

theorem BC_eq : BC = SCK.filter fun u => holdsC (fixC ++ [1, u]) t2 := by
  rw [BC, SC_eq]

theorem all_ok : (tabC.all (fun e => decide (wval gC e.2 = e.1) && decide (e.1 ∈ SC)) &&
    SC.all (fun s => tabC.any fun e => decide (e.1 = s)) &&
    gC.all (fun g => decide (g ∈ SC)) &&
    decide (tabC.map Prod.fst).Nodup &&
    [t1, t2, t3].all (fun t => decide (t.1 ∈ tabC.map Prod.snd) &&
      decide (t.2.1 ∈ tabC.map Prod.snd) && decide (t.2.2 ∈ tabC.map Prod.snd) &&
      holdsC gC t) &&
    AC.all (fun u₁ => BC.all fun u₂ => !holdsC (fixC ++ [u₁, u₂]) t3) &&
    !AC.all (fun u₁ => BC.all fun u₂ => !holdsC (fixC ++ [u₁, u₂]) t1)) = true := by
  rw [AC_eq, BC_eq, SC_eq]
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
