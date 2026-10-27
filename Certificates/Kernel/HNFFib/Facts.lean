module

public import Certificates.Kernel.HNF26729.Facts
public import Certificates.Kernel.HNFFib.Checks
public import CFSG.Certificates.Kernel.HNFFibSound
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K

public section

namespace CertificateChecks.KernelHNFFib

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier
open CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib CFSG.KS.HNF26729 CFSG.KS.HNFFib
open CFSG.KS.HNLocal CertificateChecks.KernelHNF26720 CertificateChecks.KernelHNF26729

theorem wi_valid {i : ℕ} (hi : i < 9) :
    ∀ l ∈ hnfRepWords[i]! ++ 1 :: invW hnfRepWords[i]!, Valid l := by
  have hw := valid_of (hnfRepWords_ok i hi)
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · exact hw l hl
  · rcases List.mem_cons.1 hl with rfl | hl
    · exact valid_one
    · exact valid_invW hw l hl

theorem ρ_rep {i : ℕ} (hi : i < 9) : ρJ (hnfRep hnfRepWords[i]!) =
    MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi
      (hnfRepWords[i]! ++ 1 :: invW hnfRepWords[i]!) := by
  rw [mw_eq (wi_valid hi)]
  have e : invW hnfRepWords[i]! = invWord hnfRepWords[i]! := rfl
  have e1 : letterVal hnfAB 1 = aJ := by simp [letterVal, hnfAB]
  have hw := valid_of (hnfRepWords_ok i hi)
  rw [e, wordProd_append, wordProd_cons, e1,
    wordProd_invWord hnfAB _ (fun l hl => (hw l hl).1), hnfRep, conjBy_def, mul_assoc]

theorem map_conj_inv {G H : Type} [Group G] [Monoid H] (ρ : G →* H) (g a : G)
    (ha : ρ a⁻¹ = ρ a) : ρ (g * a * g⁻¹)⁻¹ = ρ (g * a * g⁻¹) := by
  simp only [mul_inv_rev, inv_inv, map_mul, ha, mul_assoc]

theorem comm_of_closure {G : Type} [Group G] (a g1 g2 : G) (h1 : g1 * a = a * g1)
    (h2 : g2 * a = a * g2) : ∀ x ∈ Subgroup.closure ({a, g1, g2} : Set G), x * a = a * x := by
  have hle : Subgroup.closure ({a, g1, g2} : Set G) ≤ Subgroup.centralizer {a} := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 h1
    · exact Subgroup.mem_centralizer_singleton_iff.2 h2
  exact fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem ρ_rep_inv (w : List ℤ) : ρJ (hnfRep w)⁻¹ = ρJ (hnfRep w) := by
  unfold hnfRep
  rw [conjBy_def]
  exact map_conj_inv ρJ _ aJ (ρ_aJ_inv.trans ρ_aJ.symm)

theorem mem_C0 {w : List ℤ} (hw : ∀ l ∈ w, Valid3 l) : wordProd hnfGen w ∈ hnfC0 :=
  wordProd_mem_hnfC0 (plettersOK_iff.2 hw)

theorem ρ_gen_inv {w : List ℤ} (hw : ∀ l ∈ w, Valid3 l) :
    ρJ (wordProd hnfGen w)⁻¹ =
      MS (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi hnfW1 hnfW2
        (invW w) := by
  have e : invW w = invWord w := rfl
  rw [← ρ_stab _ (valid3_invW hw), e, wordProd_invWord hnfGen w (fun l hl => (hw l hl).1)]

theorem fib_gen {G : Type} [Group G] [Finite G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
    (hρ : Function.Injective ρ) (a g1 g2 β γ : G) (gen : List ℤ → G)
    (MSf : List ℤ → Matrix (Fin 133) (Fin 133) (ZMod 5))
    (hgen : ∀ w, (∀ l ∈ w, Valid3 l) → gen w ∈ Subgroup.closure ({a, g1, g2} : Set G))
    (eS : ∀ w, (∀ l ∈ w, Valid3 l) → ρ (gen w) = MSf w)
    (eSi : ∀ w, (∀ l ∈ w, Valid3 l) → ρ (gen w)⁻¹ = MSf (invW w))
    (h1 : ρ a * ρ g1 = ρ g1 * ρ a) (h2 : ρ a * ρ g2 = ρ g2 * ρ a) (hβi : ρ β⁻¹ = ρ β)
    {c : List ℕ} {us : List (List ℕ)} {N : ℕ} (vc : ∀ l ∈ decW c, Valid3 l)
    (vus : ∀ s ∈ us, ∀ l ∈ decW s, Valid3 l)
    (hyc : ρ β * ρ a * ρ β * MSf (decW c) = MSf (decW c) * ρ γ)
    (hcom : ∀ s ∈ us, MSf (decW s) * (ρ β * ρ a * ρ β) = ρ β * ρ a * ρ β * MSf (decW s))
    (hK : ∀ K : Subgroup G, (∀ s ∈ us, ∃ k ∈ K, ρ k = MSf (decW s) ∧
      ρ k⁻¹ = MSf (invW (decW s))) → N ≤ (conjS K β).ncard) :
    (conjS (Subgroup.closure ({a, g1, g2} : Set G)) γ).ncard * N ≤
      (conjS (Subgroup.closure ({a, g1, g2} : Set G)) β).ncard := by
  have hCa := comm_of_closure a g1 g2
    (hρ (by rw [map_mul ρ g1 a, map_mul ρ a g1]; exact h1.symm))
    (hρ (by rw [map_mul ρ g2 a, map_mul ρ a g2]; exact h2.symm))
  have ey : ρ (β * a * β⁻¹) = ρ β * ρ a * ρ β := by
    rw [map_mul ρ (β * a) β⁻¹, map_mul ρ β a, hβi]
  have hKy : ∀ k ∈ Subgroup.closure ({a, g1, g2} : Set G) ⊓ Subgroup.centralizer {β * a * β⁻¹},
      k * (β * a * β⁻¹) = β * a * β⁻¹ * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hk).2
  have hN := hK (Subgroup.closure ({a, g1, g2} : Set G) ⊓ Subgroup.centralizer {β * a * β⁻¹})
    fun s hs => ⟨gen (decW s), Subgroup.mem_inf.2 ⟨hgen _ (vus s hs),
      Subgroup.mem_centralizer_singleton_iff.2 (hρ (by
        rw [map_mul ρ (gen (decW s)) (β * a * β⁻¹), map_mul ρ (β * a * β⁻¹) (gen (decW s)), ey,
          eS _ (vus s hs)]
        exact hcom s hs))⟩, eS _ (vus s hs), eSi _ (vus s hs)⟩
  have hcy : gen (decW c) * γ * (gen (decW c))⁻¹ = β * a * β⁻¹ := by
    have e : β * a * β⁻¹ * gen (decW c) = gen (decW c) * γ := hρ (by
      rw [map_mul ρ (β * a * β⁻¹) (gen (decW c)), map_mul ρ (gen (decW c)) γ, ey, eS _ vc]
      exact hyc)
    rw [← e, mul_inv_cancel_right]
  have hfc := fib_card _ _ a β hCa inf_le_left hKy
  rw [conjS_eq _ (hgen _ vc) hcy] at hfc
  exact (Nat.mul_le_mul_left _ hN).trans hfc

theorem fib_bound {i j N : ℕ} (hi : i < 9) (hj : j < 9) {c : List ℕ} {us : List (List ℕ)}
    {u : ℕ} {t : List (ℕ × ℕ)} {o : List ℕ}
    (h : CFSG.KD.HNFFib.fibW hnfW1 hnfW2 hnfRepWords[i]! hnfRepWords[j]! c us u N t o = true) :
    (conjOrb hnfC0 (hnfRep hnfRepWords[j]!)).ncard * N ≤
      (conjOrb hnfC0 (hnfRep hnfRepWords[i]!)).ncard := by
  have hfin : Finite ↥JH := Finite.of_injective ρJ ρJ_injective
  have cBi' : CFSG.KS.Ord.Canon 5 133 13 CFSG.KD.HNF26729.Bi := cBi
  obtain ⟨hA1, hA2, vc, vus, hyc, hcom, hK⟩ := fib_sound CFSG.KD.FamHNSeed.consts cA cB cBi' h
  have eβ := ρ_rep hi
  have hg1 : ρJ hnfG1 = MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
      CFSG.KD.HNF26729.Bi hnfW1 := (mw_eq w1_valid).symm
  have hg2 : ρJ hnfG2 = MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
      CFSG.KD.HNF26729.Bi hnfW2 := (mw_eq w2_valid).symm
  exact fib_gen ρJ ρJ_injective aJ hnfG1 hnfG2 (hnfRep hnfRepWords[i]!) (hnfRep hnfRepWords[j]!)
    (wordProd hnfGen)
    (MS (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.HNF26729.Bi hnfW1 hnfW2)
    (fun _ hw => mem_C0 hw) (fun w hw => ρ_stab w hw) (fun _ hw => ρ_gen_inv hw)
    (by rw [ρ_aJ, hg1]; exact hA1) (by rw [ρ_aJ, hg2]; exact hA2) (ρ_rep_inv _) vc vus
    (by rw [eβ, ρ_aJ, ρ_rep hj]; exact hyc) (by rw [eβ, ρ_aJ]; exact hcom)
    (fun K hg => hK ρJ K _ eβ hg)

theorem bound5 : (conjOrb hnfC0 (hnfRep hnfRepWords[2]!)).ncard * 56 ≤
    (conjOrb hnfC0 (hnfRep hnfRepWords[5]!)).ncard :=
  fib_bound (by norm_num) (by norm_num) CFSG.KD.HNFFib.chk5

theorem bound6 : (conjOrb hnfC0 (hnfRep hnfRepWords[3]!)).ncard * 48 ≤
    (conjOrb hnfC0 (hnfRep hnfRepWords[6]!)).ncard :=
  fib_bound (by norm_num) (by norm_num) CFSG.KD.HNFFib.chk6

theorem bound8 : (conjOrb hnfC0 (hnfRep hnfRepWords[4]!)).ncard * 21 ≤
    (conjOrb hnfC0 (hnfRep hnfRepWords[8]!)).ncard :=
  fib_bound (by norm_num) (by norm_num) CFSG.KD.HNFFib.chk8

end CertificateChecks.KernelHNFFib

end
