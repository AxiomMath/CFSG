module

public import Certificates.Data.Y2L.HS
public import CFSG.Sporadic.Recognition.CoverRecipe

public section

namespace CertificateChecks.KernelY2LHS

open CFSG.OddStandard.HigherRank.G2Three.Sec2 CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.CosetTable

@[expose] def y2lGws : List (List (Fin 2 × Bool)) :=
  (y2l_hsCodes ()).map fun w => w.map fun c => (⟨c / 2 % 2, Nat.mod_lt _ (by norm_num)⟩, c % 2 == 0)

@[expose] def y2lPairs : List (List (Fin 5 × Bool) × List (Fin 2 × Bool)) :=
  (y2l_ws26 2 false).map fun r => (r, [])

theorem invW_natWord {m : ℕ} (s : List (Fin m × Bool)) :
    y2l_invW (natWord s) = natWord (FreeGroup.invRev s) := by
  simp [y2l_invW, natWord, FreeGroup.invRev, List.map_reverse]

theorem natWord_append {m : ℕ} (a b : List (Fin m × Bool)) :
    natWord (a ++ b) = natWord a ++ natWord b := List.map_append ..

theorem getD_natWord {m : ℕ} (hs : List (List (Fin m × Bool))) (i : ℕ) :
    (hs.map natWord).getD i [] = natWord (hs.getD i []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hs[i]? <;> rfl

theorem y2l_subst_eq {m : ℕ} (hs : List (List (Fin m × Bool))) (r : List (Fin 5 × Bool)) :
    y2l_subst (hs.map natWord) r = natWord (substWord hs r) := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    obtain ⟨i, b⟩ := l
    unfold y2l_subst substWord at *
    rw [List.flatMap_cons, List.flatMap_cons, natWord_append, ih]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [getD_natWord, invW_natWord]
    · simp only [if_true]
      rw [getD_natWord]

end CertificateChecks.KernelY2LHS

end
