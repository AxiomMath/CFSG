module

public import Certificates.Kernel.Ru4120.C
public import Certificates.Kernel.Ru4120.N
public import Certificates.Kernel.SporSch.Ru.Sig2251T
public import CFSG.Certificates.Kernel.LocalQTPcWSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineDelta

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Ru4120.G

open CFSG.KD.Ru4120 CFSG.KC.Kc3K CFSG.KC.Enum CFSG.KC.LQT.PcW CFSG.KC.VecK
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.A5.Kc3SporLine
open CFSG.QuasithinUnique.A5.Kc3SporPerm
open CertificateChecks.KernelVec.Ru (AT BT)

theorem n_eq : (CFSG.Sporadic.Ru.Native.ruData ()).n = 4060 := rfl

theorem ta_eq : ruTa = ((List.range 4060).map (lk AT 32)).toArray := by
  unfold ruTa
  rw [n_eq]
  congr 1
  exact List.map_congr_left fun i hi =>
    (CertificateChecks.KernelSporSch.RuSig.tables_proved i (List.mem_range.1 hi)).1

theorem tb_eq : ruTb = ((List.range 4060).map (lk BT 32)).toArray := by
  unfold ruTb
  rw [n_eq]
  congr 1
  exact List.map_congr_left fun i hi =>
    (CertificateChecks.KernelSporSch.RuSig.tables_proved i (List.mem_range.1 hi)).2

theorem rep_ta : Rep 4060 12 (TF 0) ruTa := by
  rw [ta_eq]
  exact rep_of_canon (m := 4095) (nw := 48720) (F := lk AT 32) (by rfl) (by rfl) canonA bindA

theorem rep_tb : Rep 4060 12 (TF 1) ruTb := by
  rw [tb_eq]
  exact rep_of_canon (m := 4095) (nw := 48720) (F := lk BT 32) (by rfl) (by rfl) canonB bindB

theorem rep_nodes (j : Nat) (hj : j < 486) : Rep 4060 12 (TF j) (slpTabsA ruTa ruTb progX)[j]! := by
  have hnd : ∀ j, 2 ≤ j → j < progX.length + 2 →
      TF j = pcomp 4060 12 (CFSG.KS.mask 12) (TF (progX[j - 2]!).1) (TF (progX[j - 2]!).2) := by
    intro j h2 h3
    rw [len] at h3
    have h := N.all (j / 8) (by
      have h61 : j / 8 < 61 := by omega
      exact h61)
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

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 4060)]

@[expose] noncomputable def E (a b : Γ) (j : Nat) : Γ := (slpElts a b progX).getD j 1

theorem act_node {a b : Γ} (hta : (tab 4060 a).toArray = ruTa) (htb : (tab 4060 b).toArray = ruTb)
    {j : Nat} (hj : j < 486) {p : Nat} (hp : p < 4060) :
    act 4060 (E a b j) p = pg 12 4095 (TF j) p := by
  have hinv := slp_foldl_inv (n := 4060) progX #[a, b] #[(tab 4060 a).toArray, (tab 4060 b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) valid
  have hT : progX.foldl slpStepA #[(tab 4060 a).toArray, (tab 4060 b).toArray] =
      slpTabsA ruTa ruTb progX := by
    rw [hta, htb]
    rfl
  rw [hT] at hinv
  have hs : (slpTabsA ruTa ruTb progX).size = 486 := by
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
  generalize (slpTabsA ruTa ruTb progX)[j]! = arr at hg ⊢
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

end CFSG.KD.Ru4120.G

end
