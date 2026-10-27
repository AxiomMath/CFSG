module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFStab
public import Certificates.Kernel.HNF26720.Facts
public import Certificates.Kernel.HNF26729.Checks
public import CFSG.Certificates.Kernel.HNF26729Sound
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
public import CFSG.Certificates.Kernel.Fam.Lin

public section

namespace CertificateChecks.KernelHNF26729

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier
open CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KS.HNF26729 CFSG.KS.HNLocal
open CertificateChecks.KernelHNF26720

theorem mw_eq {w : List ℤ} (hw : ∀ l ∈ w, Valid l) :
    MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi w =
      ρJ (wordProd hnfAB w) :=
  ml_word ρJ hnfAB MLJ mlj1 mljm1 mlj2 mljm2 hA2 hB3 w hw

theorem valid_invW {w : List ℤ} (hw : ∀ l ∈ w, Valid l) : ∀ l ∈ invW w, Valid l := by
  intro l hl
  simp only [invW, List.mem_map, List.mem_reverse] at hl
  obtain ⟨m, hm, rfl⟩ := hl
  have := hw m hm
  exact ⟨by omega, by omega⟩

theorem mw_inv {w : List ℤ} (hw : ∀ l ∈ w, Valid l) :
    MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi (invW w) =
      ρJ (wordProd hnfAB w)⁻¹ := by
  rw [mw_eq (valid_invW hw)]
  have e : invW w = invWord w := rfl
  rw [e, wordProd_invWord hnfAB w (fun l hl => (hw l hl).1)]

theorem w1_valid : ∀ l ∈ hnfW1, Valid l := valid_of hnfW1_ok

theorem w2_valid : ∀ l ∈ hnfW2, Valid l := valid_of hnfW2_ok

theorem ρ_aJ : ρJ aJ = OM (CFSG.KD.FamHNSeed.RW 1) := by
  rw [← hnfAB_zero, om_A]

theorem map_inv_of_sq {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5)) (a : G)
    (h : ρ a ^ 2 = 1) : ρ a⁻¹ = ρ a := by
  calc ρ a⁻¹ = ρ a⁻¹ * ρ a ^ 2 := by rw [h, mul_one]
    _ = ρ a⁻¹ * ρ a * ρ a := by rw [sq, mul_assoc]
    _ = ρ a := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

theorem ρ_aJ_inv : ρJ aJ⁻¹ = OM (CFSG.KD.FamHNSeed.RW 1) := by
  have hsq : ρJ aJ ^ 2 = 1 := by
    rw [← hnfAB_zero]
    exact hA2
  exact (map_inv_of_sq ρJ aJ hsq).trans ρ_aJ

theorem lv {l : ℤ} (hl : Valid3 l) :
    ρJ (letterVal hnfGen l) =
      ltr3 (OM (CFSG.KD.FamHNSeed.RW 1))
        (MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi hnfW1)
        (MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi (invW hnfW1))
        (MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi hnfW2)
        (MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi (invW hnfW2))
        l := by
  have h6 : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = -1 ∨ l = -2 ∨ l = -3 := by omega
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : letterVal hnfGen 1 = aJ := by simp [letterVal, hnfGen]
    rw [e, ρ_aJ, ltr3_one]
  · have e : letterVal hnfGen 2 = wordProd hnfAB hnfW1 := by simp [letterVal, hnfGen, hnfG1]
    rw [e, ← mw_eq w1_valid, ltr3_two]
  · have e : letterVal hnfGen 3 = wordProd hnfAB hnfW2 := by simp [letterVal, hnfGen, hnfG2]
    rw [e, ← mw_eq w2_valid, ltr3_three]
  · have e : letterVal hnfGen (-1) = aJ⁻¹ := by simp [letterVal, hnfGen]
    rw [e, ρ_aJ_inv, ltr3_neg_one]
  · have e : letterVal hnfGen (-2) = (wordProd hnfAB hnfW1)⁻¹ := by
      simp [letterVal, hnfGen, hnfG1]
    rw [e, ← mw_inv w1_valid, ltr3_neg_two]
  · have e : letterVal hnfGen (-3) = (wordProd hnfAB hnfW2)⁻¹ := by
      simp [letterVal, hnfGen, hnfG2]
    rw [e, ← mw_inv w2_valid, ltr3_neg_three]

theorem ρ_stab : ∀ u : List ℤ, (∀ l ∈ u, Valid3 l) →
    ρJ (wordProd hnfGen u) =
      MS (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi hnfW1 hnfW2 u
  | [], _ => by rw [wordProd_nil, map_one, MS, List.map_nil, List.prod_nil]
  | l :: u, h => by
    have ih := ρ_stab u fun x hx => h x (List.mem_cons_of_mem l hx)
    rw [MS] at ih ⊢
    rw [wordProd_cons, map_mul, ih, lv (h l List.mem_cons_self), List.map_cons, List.prod_cons]

theorem w8_valid : ∀ l ∈ hnfRepWords[8]! ++ 1 :: invW hnfRepWords[8]!, Valid l := by
  have hw := valid_of (hnfRepWords_ok 8 (by norm_num))
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · exact hw l hl
  · rcases List.mem_cons.1 hl with rfl | hl
    · exact valid_one
    · exact valid_invW hw l hl

theorem ρ_beta : ρJ (hnfRep hnfRepWords[8]!) =
    MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi
      (hnfRepWords[8]! ++ 1 :: invW hnfRepWords[8]!) := by
  rw [mw_eq w8_valid]
  have e : invW hnfRepWords[8]! = invWord hnfRepWords[8]! := rfl
  have e1 : letterVal hnfAB 1 = aJ := by simp [letterVal, hnfAB]
  have hw := valid_of (hnfRepWords_ok 8 (by norm_num))
  rw [e, wordProd_append, wordProd_cons, e1,
    wordProd_invWord hnfAB _ (fun l hl => (hw l hl).1), hnfRep, conjBy_def, mul_assoc]

theorem stab_valid {k : ℕ} (hk : k < 2) : ∀ l ∈ hnfStabWords[k]!, Valid3 l :=
  plettersOK_iff.1 (hnfStabWords_ok k hk)

theorem bound :
    240 ≤ Nat.card ↥(hnfC0 ⊓ Subgroup.centralizer ({hnfRep hnfRepWords[8]!} : Set ↥JH)) := by
  have hfin : Finite ↥JH := Finite.of_injective ρJ ρJ_injective
  have cBi' : CFSG.KS.Ord.Canon 5 133 13 CFSG.KD.HNF26729.Bi := cBi
  obtain ⟨hc0, hc1, hK⟩ := full_sound CFSG.KD.FamHNSeed.consts cA cB cBi'
    (stab_valid (k := 0) (by norm_num)) (stab_valid (k := 1) (by norm_num)) CFSG.KD.HNF26729.chk
  have e0 : ρJ (hnfStabElem 0) = MS (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
      CFSG.KD.HNF26729.Bi hnfW1 hnfW2 hnfStabWords[0]! :=
    ρ_stab _ (stab_valid (k := 0) (by norm_num))
  have e1 : ρJ (hnfStabElem 1) = MS (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
      CFSG.KD.HNF26729.Bi hnfW1 hnfW2 hnfStabWords[1]! :=
    ρ_stab _ (stab_valid (k := 1) (by norm_num))
  have mem : ∀ k < 2, ρJ (hnfStabElem k) * ρJ (hnfRep hnfRepWords[8]!) =
      ρJ (hnfRep hnfRepWords[8]!) * ρJ (hnfStabElem k) →
      hnfStabElem k ∈ hnfC0 ⊓ Subgroup.centralizer ({hnfRep hnfRepWords[8]!} : Set ↥JH) :=
    fun k hk hcm => Subgroup.mem_inf.2 ⟨hnfStabElem_mem hk,
      Subgroup.mem_centralizer_singleton_iff.2 (ρJ_injective (by rw [map_mul, map_mul]; exact hcm))⟩
  have m0 := mem 0 (by norm_num) (by rw [e0, ρ_beta]; exact hc0)
  have m1 := mem 1 (by norm_num) (by rw [e1, ρ_beta]; exact hc1)
  exact hK ρJ _ m0 m1 e0 e1

end CertificateChecks.KernelHNF26729

end
