
module

public import Certificates.Kernel.Parrott946.Checks
public import Certificates.Kernel.A45Cls.Kit
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls
  CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

abbrev P : Subgroup P45 := QP45.originalSubgroup

theorem word_mem {ng : ℕ} {G : ℕ → ℕ} {ws : List (List ℕ)}
    (hb : bindWs 45 6 ng KA.G G ws 0 = true) (hng : ng ≤ 3) {S : Subgroup P45}
    (hS : ∀ k < ng, gA' k ∈ S) {j : ℕ} (hj : j < ws.length) {g : P45} (hg : PRep 45 6 (G j) g) :
    g = ((ws.getD j []).map gA').prod ∧ g ∈ S := by
  obtain ⟨hl, he⟩ := bindWs_spec hb j hj
  rw [Nat.zero_add] at he
  have hp := wordK_prep (n := 45) (w := 6) (by norm_num) (by norm_num) (G := KA.G) (g := gA')
    ws[j] fun k hk => prep_gA k (by have := hl k hk; omega)
  rw [← he] at hp
  rw [List.getD_eq_getElem _ _ hj, prep_eq hg hp]
  refine ⟨rfl, list_prod_mem fun y hy => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  exact hS k (hl k hk)

theorem prep_pkL (L : List P45) (j : ℕ) : PRep 45 6 (pkL L j) (L.getD j 1) := prep_cOf _

theorem elsA_eq {j : ℕ} (hj : j < 12) :
    elsA.getD j 1 = ((wA.getD j []).map gA').prod ∧ elsA.getD j 1 ∈ A :=
  word_mem words.1 le_rfl (fun _ hk => gA'_mem hk) (by rw [orders.2.2.2.2.2.2.2.2.1]; exact hj)
    (prep_pkL elsA j)

theorem gA'_memP {k : ℕ} (hk : k < 2) : gA' k ∈ P := by
  change gA' k ∈ QP45.originalSubgroup
  rw [QP45_closure]
  interval_cases k
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem memP {j : ℕ} (hj : j < 8) : elsP.getD j 1 ∈ P :=
  (word_mem words.2 (by norm_num) (fun _ hk => gA'_memP hk)
    (by rw [orders.2.2.2.2.2.2.2.2.2.1]; exact hj) (prep_pkL elsP j)).2

theorem memA {j : ℕ} (hj : j < 12) : elsA.getD j 1 ∈ A := (elsA_eq hj).2

theorem t_memA : t ∈ A := memA (j := 0) (by norm_num)
theorem u_memA : u ∈ A := memA (j := 1) (by norm_num)
theorem v_memA : v ∈ A := memA (j := 2) (by norm_num)
theorem sigma1_memA : sigma1 ∈ A := memA (j := 3) (by norm_num)
theorem sigma2_memA : sigma2 ∈ A := memA (j := 4) (by norm_num)
theorem alpha1_memA : alpha1 ∈ A := memA (j := 5) (by norm_num)
theorem beta1_memA : beta1 ∈ A := memA (j := 6) (by norm_num)
theorem alpha2_memA : alpha2 ∈ A := memA (j := 7) (by norm_num)
theorem beta2_memA : beta2 ∈ A := memA (j := 8) (by norm_num)
theorem beta_memA : beta ∈ A := memA (j := 9) (by norm_num)
theorem o3b_memA : o3b ∈ A := memA (j := 10) (by norm_num)
theorem o3c_memA : o3c ∈ A := memA (j := 11) (by norm_num)

theorem u_memP : u ∈ P := memP (j := 0) (by norm_num)
theorem sigma1_memP : sigma1 ∈ P := memP (j := 1) (by norm_num)
theorem sigma2_memP : sigma2 ∈ P := memP (j := 2) (by norm_num)
theorem alpha1_memP : alpha1 ∈ P := memP (j := 3) (by norm_num)
theorem beta1_memP : beta1 ∈ P := memP (j := 4) (by norm_num)
theorem alpha2_memP : alpha2 ∈ P := memP (j := 5) (by norm_num)
theorem beta2_memP : beta2 ∈ P := memP (j := 6) (by norm_num)
theorem beta_memP : beta ∈ P := memP (j := 7) (by norm_num)

theorem v_eq : v = f45 * x45 := by
  have h := (elsA_eq (j := 2) (by norm_num)).1
  have e : (wA.getD 2 []).map gA' = [f45, x45] := rfl
  rw [e, List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at h
  exact h

theorem card_P : Nat.card P = 25920 := by
  rw [card_group QP45 QP45_ok, QP45_valid.2]

theorem v_not_mem_P : v ∉ P := by
  intro hv
  have hf : f45 ∈ P := by
    have e : f45 = v * x45⁻¹ := by rw [v_eq, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hv (inv_mem (gA'_memP (k := 0) (by norm_num)))
  have hle : A ≤ P := by
    rw [← closure_gA, closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 3 := hk
    interval_cases k
    · exact gA'_memP (by norm_num)
    · exact gA'_memP (by norm_num)
    · exact hf
  have := Subgroup.card_le_of_le hle
  rw [card_A, card_P] at this
  omega

theorem card_cent_s1 :
    Nat.card ↥(A ⊓ centralizer ({sigma1} : Set P45)) = 648 := by
  obtain ⟨h0, h1, h2, -, -, -, -, -, -, bt, -⟩ := binds
  have := (class_A K1.h (prep_gens h0 h1 h2) K1.cl K1.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) K1.k).1
  change 80 * _ = _ at this
  omega

theorem card_cent_s12 :
    Nat.card ↥(A ⊓ centralizer ({sigma1 * sigma2} : Set P45)) = 216 := by
  obtain ⟨-, -, -, h0, h1, h2, -, -, -, -, bt, -⟩ := binds
  have := (class_A K12.h (prep_gens h0 h1 h2) K12.cl K12.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) K12.k).1
  change 240 * _ = _ at this
  omega

theorem card_cent_s12i :
    Nat.card ↥(A ⊓ centralizer ({sigma1 * sigma2⁻¹} : Set P45)) = 108 := by
  obtain ⟨-, -, -, -, -, -, h0, h1, h2, -, -, bt, -⟩ := binds
  have := (class_A K12i.h (prep_gens h0 h1 h2) K12i.cl K12i.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) K12i.k).1
  change 480 * _ = _ at this
  omega

theorem card_cent_s2 (h : u * sigma1 * u⁻¹ = sigma2) :
    Nat.card ↥(A ⊓ centralizer ({sigma2} : Set P45)) = 648 := by
  rw [← h, card_cent_conj u_memA]
  exact card_cent_s1

theorem fixC_t : fixC t = 13 := by rw [← fixK_eq (prep_cOf t)]; exact fixes.1
theorem fixC_u : fixC u = 13 := by rw [← fixK_eq (prep_cOf u)]; exact fixes.2.1
theorem fixC_v : fixC v = 7 := by rw [← fixK_eq (prep_cOf v)]; exact fixes.2.2

theorem card_cent_t (h2 : t * t = 1) (h1 : t ≠ 1) :
    Nat.card ↥(A ⊓ centralizer ({t} : Set P45)) = 1152 := by
  rw [card_cent_eq t_memA h2 h1, fixC_t]
  rfl

theorem card_cent_u (h2 : u * u = 1) (h1 : u ≠ 1) :
    Nat.card ↥(A ⊓ centralizer ({u} : Set P45)) = 1152 := by
  rw [card_cent_eq u_memA h2 h1, fixC_u]
  rfl

theorem card_cent_v (h2 : v * v = 1) (h1 : v ≠ 1) :
    Nat.card ↥(A ⊓ centralizer ({v} : Set P45)) = 96 := by
  rw [card_cent_eq v_memA h2 h1, fixC_v]
  rfl

theorem filter_cent (g : P45) :
    ((elemsT QA45).filter (fun c => c * g = g * c)).length =
      Nat.card ↥(A ⊓ centralizer ({g} : Set P45)) :=
  (card_inf_centralizer QA45 QA45_ok g).symm

end CertificateChecks.Parrott946

end
