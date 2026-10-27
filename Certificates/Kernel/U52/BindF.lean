module

public import Certificates.Kernel.U52.LettersF
public import CFSG.Certificates.Kernel.U52.EvSound
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.LocalQTCovTPrim

public section

namespace CertificateChecks.KernelU52F

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum

theorem lf_eq : ∀ i < 5, (burnsideF48t_u52eLArr ())[i]! = unpack 462 9 (LFP i) :=
  fun i hi => arrBind_sound (lfBind i hi)

theorem lfi_eq : ∀ i < 5, (burnsideF48t_u52eLInv ())[i]! = unpack 462 9 (LFPI i) := by
  intro i hi
  have hs : (burnsideF48t_u52eLArr ()).size = 5 := by decide +kernel
  rw [burnsideF48t_u52eLInv, getElem!_pos _ i (by simp [hs, hi]), Array.getElem_map,
    ← getElem!_pos _ i (by omega), lf_eq i hi]
  exact pinvCand_unpack (allN_spec lfPerm i hi)

theorem lf_range : ∀ i < 5, ∀ x < 462,
    pg 9 (mask 9) (LFP i) x < 462 ∧ pg 9 (mask 9) (LFPI i) x < 462 := fun i hi x hx =>
  ⟨((CFSG.KC.LQT.Cov.T.perm_facts (allN_spec lfPerm i hi)).1 x hx).1,
    ((CFSG.KC.LQT.Cov.T.perm_facts (allN_spec lfiPerm i hi)).1 x hx).1⟩

theorem evF_eq (wd : List (Fin 5 × Bool)) :
    burnsideF48t_evA 462 (burnsideF48t_u52eLArr ()) (burnsideF48t_u52eLInv ()) wd =
      unpack 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd) :=
  (evA_unpack (by norm_num) (by norm_num) lf_eq lfi_eq lf_range wd).1

end CertificateChecks.KernelU52F

end
