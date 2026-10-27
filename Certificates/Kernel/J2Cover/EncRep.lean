module

public import Certificates.Kernel.J2Cover.ModelsBind

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.J2Cover.Models

theorem wordP_appendE : ∀ (w : List Nat) (l : Nat),
    wordP (w ++ [l]) = pcomp 315 9 (mask 9) (wordP w) (letP l)
  | [], l => (CFSG.KC.J2Cover.pcomp_id (letP_canon l)).1.trans (CFSG.KC.J2Cover.pcomp_id (letP_canon l)).2.symm
  | k :: w, l => by
    have e : wordP (k :: w ++ [l]) = pcomp 315 9 (mask 9) (letP k) (wordP (w ++ [l])) := rfl
    rw [e, wordP_appendE w l]
    exact (CFSG.KC.J2Cover.pcomp_assoc (letP_canon k) (wordP_canon w) (letP_canon l)).symm

theorem cosetWordAux_eqE : ∀ (n i : Nat), i < 4725 → dpK i < n →
    wordP (cosetWordAux n i) = RPT i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, hi, hd => by
    obtain ⟨-, -, h0, h1⟩ := rep_facts i hi
    unfold cosetWordAux
    by_cases hz : i = 0
    · subst hz
      rw [ite_eq_left rfl, h0 rfl]
      rfl
    · obtain ⟨hp, hdp, he⟩ := h1 hz
      rw [ite_eq_right_of_eq_false _ _ (eq_false hz), cosetPar_eq, cosetLab_eq,
        getElem!_unpack hi, getElem!_unpack hi, wordP_appendE]
      change pcomp 315 9 (mask 9) (wordP (cosetWordAux n (cpK i))) (letP (clK i)) = RPT i
      rw [cosetWordAux_eqE n (cpK i) hp (by omega), he]

theorem repArrs_eqE (i : Nat) (hi : i < 4725) : repArrs[i]! = unpack 315 9 (RPT i) := by
  unfold repArrs
  rw [getElem!_ofFn' hi, wordArr_eq]
  unfold cosetWord
  rw [cosetWordAux_eqE 64 i hi (rep_facts i hi).1]

end CertificateChecks.KernelJ2Cover

end
