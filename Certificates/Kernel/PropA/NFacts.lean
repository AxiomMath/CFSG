module

public import Certificates.Kernel.PropA.KFacts
public import Certificates.Kernel.PropA.NChk
public import CFSG.Certificates.Kernel.Spor.PCosSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NormalSmall

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb
  CFSG.KS.PRec CFSG.KS.PCos CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA

theorem pa450010_N_of {b : Bool} {k cnt : ℕ}
    {G GI T PL POS SRT SRI W E : ℕ → ℕ}
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 960 k G GI cnt T PL 4
      (pa450010S b) (pa450010SI b) pa450010wCKX = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) false G GI k cnt T PL POS SRT SRI 0 960 = true)
    {S3 : ℕ} (hpT : PRep 28 5 S3 pT)
    (hW : bAnd(Nat.beq (W 0) (pidn 28 5), bAnd(Nat.beq (W 1) S3, bAnd(Nat.beq (W 2)
      (pcomp 28 5 (mask 5) S3 pa450010XD.R), Nat.beq (W 3) pa450010XD.R))) = true)
    (hcos : cosK 28 5 (mask 5) cnt T pa450010J.cnt pa450010J.T 4 W k G pa450010XD.R E = true) :
    ∀ N : Subgroup (Perm (Fin 28)), N ≤ K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) →
      (N.subgroupOf (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))))).Normal →
        jOf D28 pa450010x ≤ N → pa450010x ∉ N → Nat.card ↥N ≤ 120 := by
  intro N hNle hNnorm hJN hxN
  obtain ⟨xK, hxK, -, hmemK, -, hk, hg, -⟩ := pa450010_rec (by norm_num) hd hsl
  obtain ⟨xJ, hxJ, -, hmemJ, -⟩ := pa450010_J_rec
  have hKeq := (pa450010_K_facts b).1
  simp only [bAnd_eq, Bool.and_eq_true] at hW
  obtain ⟨hW0, hW1, hW2, hW3⟩ := hW
  have hv : ∀ i < 4, PRep 28 5 (W i) ([1, pT, pT * pa450010x, pa450010x].getD i 1) := by
    intro i hi
    interval_cases i
    · rw [Nat.eq_of_beq_eq_true hW0]
      exact prep_pidn (by norm_num) (by norm_num)
    · rw [Nat.eq_of_beq_eq_true hW1]
      exact hpT
    · rw [Nat.eq_of_beq_eq_true hW2]
      exact prep_pcomp (by norm_num) hpT pa450010_prepX
    · rw [Nat.eq_of_beq_eq_true hW3]
      exact pa450010_prepX
  have hgC : ∀ c < k, pa450010wv b 4 pa450010wCKX[c]! ∈
      K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) := by
    intro c hc
    rw [hKeq]
    exact pa450010_gen_mem b 4 _ (by omega)
  have hcosS := cosK_spec (by norm_num) hxK hxJ hv hg pa450010_prepX hcos
  have hcov : ∀ g ∈ N, g ∈ jOf D28 pa450010x ∨ pT⁻¹ * g ∈ jOf D28 pa450010x ∨
      (pT * pa450010x)⁻¹ * g ∈ jOf D28 pa450010x := by
    intro g hgN
    have hgC' := hNle hgN
    rw [hKeq] at hgC'
    obtain ⟨q, hq, rfl⟩ := (hmemK _).1 hgC'
    obtain ⟨j, hj, hcase⟩ := hcosS q hq
    have hyJ : xJ j ∈ jOf D28 pa450010x := by
      rw [pa450010_jOf_eq]
      exact (hmemJ _).2 ⟨j, hj, rfl⟩
    have hyN : xJ j ∈ N := hJN hyJ
    rcases hcase with ⟨i, hi, e⟩ | ⟨c, hc, e⟩
    · interval_cases i
      · left
        have e' : xK q = xJ j := by
          rw [e]
          exact one_mul _
        rw [e']
        exact hyJ
      · right
        left
        have e' : pT⁻¹ * xK q = xJ j := by
          rw [e]
          change pT⁻¹ * (pT * xJ j) = xJ j
          group
        rw [e']
        exact hyJ
      · right
        right
        have e' : (pT * pa450010x)⁻¹ * xK q = xJ j := by
          rw [e]
          change (pT * pa450010x)⁻¹ * (pT * pa450010x * xJ j) = xJ j
          group
        rw [e']
        exact hyJ
      · exfalso
        have e' : pa450010x = xK q * (xJ j)⁻¹ := by
          rw [e]
          change pa450010x = pa450010x * xJ j * (xJ j)⁻¹
          group
        exact hxN (e' ▸ N.mul_mem hgN (N.inv_mem hyN))
    · exfalso
      set gc := pa450010wv b 4 pa450010wCKX[c]!
      have e' : pa450010x = gc * xK q * gc⁻¹ * (xJ j)⁻¹ * (xK q)⁻¹ := by
        calc pa450010x = pa450010x * xK q * xJ j * gc * gc⁻¹ * (xJ j)⁻¹ * (xK q)⁻¹ := by group
          _ = gc * xK q * gc⁻¹ * (xJ j)⁻¹ * (xK q)⁻¹ := by rw [e]
      have hconj : gc * xK q * gc⁻¹ ∈ N :=
        Subgroup.mem_subgroupOf.mp (hNnorm.conj_mem ⟨xK q, hNle hgN⟩
          (Subgroup.mem_subgroupOf.mpr hgN) ⟨gc, hgC c hc⟩)
      exact hxN (e' ▸ N.mul_mem (N.mul_mem hconj (N.inv_mem hyN)) (N.inv_mem hgN))
  have hcard := CFSG.EvenSporadicStandard.M12Std.Rbc.card_le_two_mul_of_subset_cosets
    (J := jOf D28 pa450010x) (N := N) (w₁ := pT) (w₂ := pT * pa450010x) (x := pa450010x) hJN
    (by group) hxN hcov
  rw [pa450010_card_J] at hcard
  omega

theorem pa450010_normal_small (b : Bool) :
    ∀ N : Subgroup (Perm (Fin 28)), N ≤ K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) →
      (N.subgroupOf (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))))).Normal →
        jOf D28 pa450010x ≤ N → pa450010x ∉ N → Nat.card ↥N ≤ 120 := by
  cases b
  · exact pa450010_N_of (b := false) (W := pa450010NW1) (E := pa450010NE1) (S3 := pa450010S1 3)
      pa450010_CKX1_hd pa450010_CKX1_sl (pa450010_prepS false 3 (by norm_num))
      pa450010_NW1 pa450010_N1_cos
  · exact pa450010_N_of (b := true) (W := pa450010NW2) (E := pa450010NE2) (S3 := pa450010S2 3)
      pa450010_CKX2_hd pa450010_CKX2_sl (pa450010_prepS true 3 (by norm_num))
      pa450010_NW2 pa450010_N2_cos

end CertificateChecks.KernelPropA

end
