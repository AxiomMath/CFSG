module

public import Certificates.Kernel.He4049.C
public import Certificates.Kernel.He4049.N
public import CFSG.Certificates.Kernel.LocalQTPcWSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He4049.G

open CFSG.KD.He4049 CFSG.KC.Enum CFSG.KC.LQT.PcW
open CFSG.QuasithinUnique.K1.SporadicPerm

theorem rep_ta : Rep 8330 14 (TF 0) TA :=
  rep_of_canon (m := 16383) (nw := 116620) (F := pg 14 16383 (TF 0)) (by rfl) (by rfl) canonA bindA

theorem rep_tb : Rep 8330 14 (TF 1) TB :=
  rep_of_canon (m := 16383) (nw := 116620) (F := pg 14 16383 (TF 1)) (by rfl) (by rfl) canonB bindB

theorem rep_nodes (j : Nat) (hj : j < 343) : Rep 8330 14 (TF j) (slpTabsA TA TB progX)[j]! := by
  have hnd : ∀ j, 2 ≤ j → j < progX.length + 2 →
      TF j = pcomp 8330 14 (CFSG.KS.mask 14) (TF (progX[j - 2]!).1) (TF (progX[j - 2]!).2) := by
    intro j h2 h3
    rw [len] at h3
    have h := N.all (j / 8) (by
      have h43 : j / 8 < 43 := by omega
      exact h43)
    unfold famN at h
    have hlo : Nat.mul (j / 8) 8 ≤ j := by
      rw [Nat.mul_eq]
      omega
    have hhi : j < Nat.mul (j / 8) 8 + 8 := by
      rw [Nat.mul_eq]
      omega
    rw [nodesT_spec h hlo hhi h2 (by rw [len]; omega)]
    exact CFSG.KS.PF.mulW_eq_pcomp _ _ (by norm_num) (by norm_num)
  exact slp_rep (by norm_num) (by norm_num) rep_ta rep_tb valid hnd j (by rw [len]; omega)

theorem size_foldl_slpStepA : ∀ (l : List (Nat × Nat)) (acc : Array (Array Nat)),
    (l.foldl slpStepA acc).size = acc.size + l.length
  | [], acc => rfl
  | p :: l, acc => by
    rw [List.foldl_cons, size_foldl_slpStepA l, List.length_cons]
    simp [slpStepA]
    omega

section Group

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 8330)]

@[expose] noncomputable def E (a b : Γ) (j : Nat) : Γ := (slpElts a b progX).getD j 1

theorem act_node {a b : Γ} (hta : (tab 8330 a).toArray = TA) (htb : (tab 8330 b).toArray = TB)
    {j : Nat} (hj : j < 343) {p : Nat} (hp : p < 8330) :
    act 8330 (E a b j) p = pg 14 16383 (TF j) p := by
  have hinv := slp_foldl_inv (n := 8330) progX #[a, b] #[(tab 8330 a).toArray, (tab 8330 b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) valid
  have hT : progX.foldl slpStepA #[(tab 8330 a).toArray, (tab 8330 b).toArray] =
      slpTabsA TA TB progX := by
    rw [hta, htb]
    rfl
  rw [hT] at hinv
  have hs : (slpTabsA TA TB progX).size = 343 := by
    unfold slpTabsA
    rw [size_foldl_slpStepA, len]
    rfl
  have h1 := hinv.2 j (by rw [hs]; exact hj)
  have hr := rep_nodes j hj
  unfold E act
  have e : (progX.foldl eltStep #[a, b]) = slpElts a b progX := rfl
  rw [e] at h1
  rw [h1, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have hg := rep_get hr p hp
  rw [getElem!_def] at hg
  generalize (slpTabsA TA TB progX)[j]! = arr at hg ⊢
  cases hq : arr[p]? with
  | none =>
    rw [hq] at hg
    rw [Option.getD_none]
    exact hg
  | some x =>
    rw [hq] at hg
    rw [Option.getD_some]
    exact hg

end Group

end CFSG.KD.He4049.G

end
