module

public import Certificates.Kernel.U52.Letters
public import CFSG.Certificates.Kernel.U52.EvSound
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.LocalQTCovTPrim

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum

theorem getD_map_toArray {β : Type} (f : β → Array Nat) (l : List β) (d : β) {j : Nat}
    (hj : j < l.length) : (l.map f).toArray[j]! = f (l.getD j d) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getElem?_eq_getElem hj]

theorem l_eq : ∀ i < 4, burnsideF48t_u52LArr[i]! = unpack 462 9 (LP i) :=
  fun i hi => arrBind_sound (lpBind i hi)

theorem li_eq : ∀ i < 4, (burnsideF48t_u52LInv ())[i]! = unpack 462 9 (LPI i) := by
  intro i hi
  have hs : burnsideF48t_u52LArr.size = 4 := by decide +kernel
  rw [burnsideF48t_u52LInv, getElem!_pos _ i (by simp [hs, hi]), Array.getElem_map,
    ← getElem!_pos _ i (by omega), l_eq i hi]
  exact pinvCand_unpack (allN_spec lpPerm i hi)

theorem l_range : ∀ i < 4, ∀ x < 462,
    pg 9 (mask 9) (LP i) x < 462 ∧ pg 9 (mask 9) (LPI i) x < 462 := fun i hi x hx =>
  ⟨((CFSG.KC.LQT.Cov.T.perm_facts (allN_spec lpPerm i hi)).1 x hx).1,
    ((CFSG.KC.LQT.Cov.T.perm_facts (allN_spec lpiPerm i hi)).1 x hx).1⟩

theorem ev_eq (wd : List (Fin 4 × Bool)) :
    burnsideF48t_evA 462 burnsideF48t_u52LArr (burnsideF48t_u52LInv ()) wd =
      unpack 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LP LPI wd) :=
  (evA_unpack (by norm_num) (by norm_num) l_eq li_eq l_range wd).1

end CertificateChecks.KernelU52

end
