module

public import Certificates.Kernel.G23F48.OrbitCheck
public import CFSG.Certificates.Kernel.G23F48.Reach

public section

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.ONSchreier

variable {H : Subgroup (Equiv.Perm (Fin 728))} {σ : ℕ → Equiv.Perm (Fin 728)}

theorem orbit_X_0 (hσ : ∀ s < 4, PRep 728 (burnsideF48t_g23Gens ())[s]! (σ s) ∧ σ s ∈ H) :
    ∃ O : Finset (Fin 728), O.card = 364 ∧ ∀ r ∈ O, ∃ g ∈ H, g 0 = r := by
  obtain ⟨O, hc, hO⟩ := orbit_of_reachOK hσ reach_ok.1 (by norm_num) nodup_ok.1
  exact ⟨O, hc.trans nodup_ok.2.2.2.2.1, hO⟩

theorem orbit_X_364 (hσ : ∀ s < 4, PRep 728 (burnsideF48t_g23Gens ())[s]! (σ s) ∧ σ s ∈ H) :
    ∃ O : Finset (Fin 728), O.card = 364 ∧ ∀ r ∈ O, ∃ g ∈ H, g 364 = r := by
  obtain ⟨O, hc, hO⟩ := orbit_of_reachOK hσ reach_ok.2.1 (by norm_num) nodup_ok.2.1
  exact ⟨O, hc.trans nodup_ok.2.2.2.2.2.1, hO⟩

theorem orbit_P1 (hσ : ∀ s < 3, PRep 728 burnsideF48t_g23P1Arr[s]! (σ s) ∧ σ s ∈ H) :
    ∃ O : Finset (Fin 728), O.card = 4 ∧ ∀ r ∈ O, ∃ g ∈ H, g 364 = r := by
  obtain ⟨O, hc, hO⟩ := orbit_of_reachOK hσ reach_ok.2.2.1 (by norm_num) nodup_ok.2.2.1
  exact ⟨O, hc.trans nodup_ok.2.2.2.2.2.2.1, hO⟩

theorem orbit_P2 (hσ : ∀ s < 3, PRep 728 burnsideF48t_g23P2Arr[s]! (σ s) ∧ σ s ∈ H) :
    ∃ O : Finset (Fin 728), O.card = 4 ∧ ∀ r ∈ O, ∃ g ∈ H, g 0 = r := by
  obtain ⟨O, hc, hO⟩ := orbit_of_reachOK hσ reach_ok.2.2.2 (by norm_num) nodup_ok.2.2.2.1
  exact ⟨O, hc.trans nodup_ok.2.2.2.2.2.2.2, hO⟩

end CFSG.KC.G23F48

end
