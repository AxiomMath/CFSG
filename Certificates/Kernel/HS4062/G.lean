module

public import Certificates.Kernel.HS4062.C
public import Certificates.Kernel.HS4062.N
public import Certificates.Kernel.LocalQT.SV.C4126TB
public import CFSG.Certificates.Kernel.LocalQTPcWSound
public import CFSG.Certificates.Kernel.HeFixKFix
public import CFSG.Sporadic.Schreier.PairHSOrder

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS4062.G

open CFSG.KD.HS4062 CFSG.KC.Enum CFSG.KC.LQT.PcW
open CFSG.Sporadic.Schreier (hsP hsGen hsGen_mem_P rep_hsGen hs_baseFaithful hsP_eq_original)
open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] noncomputable def hsA : ↥hsP := ⟨hsGen 0, hsGen_mem_P 0 (by norm_num)⟩

@[expose] noncomputable def hsB : ↥hsP := ⟨hsGen 1, hsGen_mem_P 1 (by norm_num)⟩

theorem mask12 : CFSG.KS.mask 12 = 4095 := by decide +kernel

theorem tab_gen {k : Nat} (hk : k < 2) (g : ↥hsP)
    (hg : (g : Equiv.Perm (Fin 3850)) = hsGen k) :
    (tab 3850 g).toArray = ((List.range 3850).map (pg 12 4095 (CFSG.KD.LQT.C4126.HS.F k))).toArray := by
  congr 1
  apply List.ext_getElem (by simp [CFSG.QuasithinUnique.K1.SporadicPerm.tab])
  intro i h1 h2
  have hi : i < 3850 := by simpa [CFSG.QuasithinUnique.K1.SporadicPerm.tab] using h1
  simp only [CFSG.QuasithinUnique.K1.SporadicPerm.tab, List.getElem_map, List.getElem_finRange,
    List.getElem_range]
  have hr := rep_hsGen (k := k) (by omega) ⟨i, hi⟩
  have e : (g • (⟨i, hi⟩ : Fin 3850) : Fin 3850) = hsGen k ⟨i, hi⟩ := by
    rw [← hg]
    rfl
  rw [Fin.cast_mk, e, ← hr, CFSG.KD.LQT.C4126.hsStrong_get hk, CFSG.KC.HeFixK.unpack_getElem! hi,
    mask12]

theorem tabA : (tab 3850 hsA).toArray = TA := by
  rw [tab_gen (k := 0) (by norm_num) hsA rfl, TA, ← Nat.eq_of_beq_eq_true eqA]

theorem tabB : (tab 3850 hsB).toArray = TB := by
  rw [tab_gen (k := 1) (by norm_num) hsB rfl, TB, ← Nat.eq_of_beq_eq_true eqB]

theorem rep_ta : Rep 3850 12 (TF 0) TA :=
  rep_of_canon (m := 4095) (nw := 46200) (F := pg 12 4095 (TF 0)) (by rfl) (by rfl) canonA bindA

theorem rep_tb : Rep 3850 12 (TF 1) TB :=
  rep_of_canon (m := 4095) (nw := 46200) (F := pg 12 4095 (TF 1)) (by rfl) (by rfl) canonB bindB

theorem rep_nodes (j : Nat) (hj : j < 203) : Rep 3850 12 (TF j) (slpTabsA TA TB progX)[j]! := by
  have hnd : ∀ j, 2 ≤ j → j < progX.length + 2 →
      TF j = pcomp 3850 12 (CFSG.KS.mask 12) (TF (progX[j - 2]!).1) (TF (progX[j - 2]!).2) := by
    intro j h2 h3
    rw [len] at h3
    have h := N.all (j / 8) (by
      have h26 : j / 8 < 26 := by omega
      exact h26)
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

@[expose] noncomputable def E (j : Nat) : ↥hsP := (slpElts hsA hsB progX).getD j 1

theorem act_node {j : Nat} (hj : j < 203) {p : Nat} (hp : p < 3850) :
    act 3850 (E j) p = pg 12 4095 (TF j) p := by
  have hinv := slp_foldl_inv (n := 3850) progX #[hsA, hsB]
    #[(tab 3850 hsA).toArray, (tab 3850 hsB).toArray] (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) valid
  have hT : progX.foldl slpStepA #[(tab 3850 hsA).toArray, (tab 3850 hsB).toArray] =
      slpTabsA TA TB progX := by
    rw [tabA, tabB]
    rfl
  rw [hT] at hinv
  have hs : (slpTabsA TA TB progX).size = 203 := by
    unfold slpTabsA
    rw [size_foldl_slpStepA, len]
    rfl
  have h1 := hinv.2 j (by rw [hs]; exact hj)
  have hr := rep_nodes j hj
  unfold E act
  have e : (progX.foldl eltStep #[hsA, hsB]) = slpElts hsA hsB progX := rfl
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

theorem base (g : ↥hsP)
    (hg : ∀ p ∈ B, act 3850 g p = p) : g = 1 := by
  have hf := hs_baseFaithful
  rw [← hsP_eq_original] at hf
  refine Subtype.ext (hf g g.2 fun x hx => Fin.ext ?_)
  have hx' : (x : Nat) ∈ B := hx
  have := hg x hx'
  rw [act_eq] at this
  exact this

end CFSG.KD.HS4062.G

end
