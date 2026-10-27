module

public import Certificates.Kernel.Misc.OmegaSix.TransChecks
public import Certificates.Kernel.Misc.OmegaSix.Final
public import CFSG.Certificates.Kernel.Misc.OmegaSixOSound

public section

namespace CFSG.KD.OmegaSix.Trans

open CFSG.KD.OmegaSix CFSG.KD.BfsK CFSG.CGT.Foote82.OmegaSix CFSG.KC.OmegaSix
  CFSG.ClassicalInvolution.Solomon73.Yamaki

theorem transCheck_ok : transCheck () = true := by
  have T := omega_inv oMatA oMatB oHead oTab
  unfold transCheck omegaEnum
  rw [List.all_eq_true]
  intro n hn
  have h := List.all_eq_true.1 kNS n hn
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · right
    obtain ⟨p, hp, hpn⟩ := List.any_eq_true.1 h
    have hw := List.all_eq_true.1 kTW p hp
    unfold witK at hw
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hw
    have hs : p.getD 1 0 < (bfsEnum (genA6 ()) 25920).elems.size := by
      rw [T.1.1]
      exact hw.1
    rw [Array.any_eq_true]
    refine ⟨p.getD 1 0, hs, ?_⟩
    rw [← getElem!_pos (bfsEnum (genA6 ()) 25920).elems (p.getD 1 0) hs, T.1.2.2.2.1 _ hw.1]
    have e : v0 = 2 ^ 4 := rfl
    rw [e, arrF_get_col _ 4 (by norm_num), hw.2]
    exact hpn

theorem countCheck_ok : countCheck () = true := by decide +kernel

end CFSG.KD.OmegaSix.Trans

end
