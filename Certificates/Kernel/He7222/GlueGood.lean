module

public import Certificates.Kernel.He7222.GlueScan
public import Certificates.Kernel.He7222.GlueWp
public import Certificates.Kernel.He7222.GlueWords
public import CFSG.Certificates.Kernel.He7222.GoodSound
public import CFSG.Certificates.Kernel.Misc.WordPtsGroup
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PrimSound
public import Certificates.Kernel.Sporadic.Fi22.C3151

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223

theorem iter_eq {f : ℕ → ℕ} {y : Equiv.Perm (Fin 8330)} (hf : ∀ x : Fin 8330, f x = y x) :
    ∀ (i : ℕ) (x : Fin 8330), f^[i] x = ((y ^ i) x : ℕ)
  | 0, x => rfl
  | i + 1, x => by
    rw [Function.iterate_succ_apply, hf x, iter_eq hf i, pow_succ, Equiv.Perm.mul_apply]

theorem oK_eq {f : ℕ → ℕ} {y τ : Equiv.Perm (Fin 8330)} {τP p i : ℕ}
    (hf : ∀ x : Fin 8330, f x = y x) (hτ : PRep 8330 14 τP τ) (hp : y ^ p = 1) (hi : i ≤ p)
    (x : Fin 8330) : oK 14 (mask 14) f τP p i x = ((y ^ i * τ * (y ^ i)⁻¹) x : ℕ) := by
  have e : y ^ (p - i) = (y ^ i)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel hi, hp]
  unfold oK
  change powF f i (pg 14 (mask 14) τP (powF f (p - i) x)) = _
  rw [powF_eq, powF_eq, iter_eq hf, hτ, iter_eq hf, e, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem prodO_mem {f : ℕ → ℕ} {y τ : Equiv.Perm (Fin 8330)} {τP p : ℕ}
    (hf : ∀ x : Fin 8330, f x = y x) (hτ : PRep 8330 14 τP τ) (hp : y ^ p = 1) (mk : ℕ) :
    ∀ n ≤ p, ∃ g ∈ orbSub y τ, ∀ x : Fin 8330,
      (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q)
        (fun i ih q => ih (nIf(Nat.beq (Nat.land (Nat.shiftRight mk i) (nat_lit 1)) (nat_lit 1),
          oK 14 (mask 14) f τP p i q, q))) n (x : ℕ) : ℕ) = g x
  | 0, _ => ⟨1, (orbSub y τ).one_mem, fun x => rfl⟩
  | n + 1, hn => by
    obtain ⟨g, hg, hgx⟩ := prodO_mem hf hτ hp mk n (by omega)
    cases hb : Nat.beq (Nat.land (Nat.shiftRight mk n) (nat_lit 1)) (nat_lit 1) with
    | true =>
      refine ⟨g * (y ^ n * τ * (y ^ n)⁻¹), (orbSub y τ).mul_mem hg (conj_mem_orbSub y τ n),
        fun x => ?_⟩
      change (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q)
        (fun i ih q => ih (nIf(Nat.beq (Nat.land (Nat.shiftRight mk i) (nat_lit 1)) (nat_lit 1),
          oK 14 (mask 14) f τP p i q, q))) n
        (nIf(Nat.beq (Nat.land (Nat.shiftRight mk n) (nat_lit 1)) (nat_lit 1),
          oK 14 (mask 14) f τP p n (x : ℕ), (x : ℕ))) : ℕ) = _
      rw [hb]
      change (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q)
        (fun i ih q => ih (nIf(Nat.beq (Nat.land (Nat.shiftRight mk i) (nat_lit 1)) (nat_lit 1),
          oK 14 (mask 14) f τP p i q, q))) n (oK 14 (mask 14) f τP p n (x : ℕ)) : ℕ) = _
      rw [oK_eq hf hτ hp (by omega), hgx]
      simp only [Equiv.Perm.mul_apply]
    | false =>
      refine ⟨g, hg, fun x => ?_⟩
      change (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q)
        (fun i ih q => ih (nIf(Nat.beq (Nat.land (Nat.shiftRight mk i) (nat_lit 1)) (nat_lit 1),
          oK 14 (mask 14) f τP p i q, q))) n
        (nIf(Nat.beq (Nat.land (Nat.shiftRight mk n) (nat_lit 1)) (nat_lit 1),
          oK 14 (mask 14) f τP p n (x : ℕ), (x : ℕ))) : ℕ) = _
      rw [hb]
      exact hgx x

theorem orbSub_le_heP {y τ : Equiv.Perm (Fin 8330)} (hy : y ∈ heP) (hτ : τ ∈ heP) :
    orbSub y τ ≤ heP := by
  rw [orbSub, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact heP.mul_mem (heP.mul_mem (heP.pow_mem hy j) hτ) (heP.inv_mem (heP.pow_mem hy j))

theorem hconcl_of_goodK {τ y : Equiv.Perm (Fin 8330)} {τP : ℕ}
    (hτP : PRep 8330 14 τP τ) (hτ : τ ∈ heP) (hy : y ∈ heP) {f : ℕ → ℕ}
    (hf : ∀ x : Fin 8330, f x = y x) {rec : List ℕ}
    (hg : goodK 14 (mask 14) f τP LU LUI DW R5 R7 rec = true) : HConcl τ y := by
  intro _ _ hcomm
  obtain ⟨hp0, hpow, hcase⟩ := goodK_sound hg
  set p := getS rec 0 with hpdef
  have hyp : y ^ p = 1 := by
    refine CFSG.KC.WordPts.eq_of_pts baseFaithful_heP (heP.pow_mem hy p) heP.one_mem
      fun x hx => Fin.ext ?_
    have hx5 : (x : ℕ) < 5 := by
      simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    rw [← iter_eq hf p x, hpow x hx5]
    rfl
  rcases hcase with ⟨-, hj, hq, hne⟩ | ⟨-, -, -, hd3, -, hb⟩
  · exfalso
    apply hne
    set jj := getS rec 2
    set q := getS rec 3
    obtain ⟨qF, hqF⟩ : ∃ qF : Fin 8330, (qF : ℕ) = q := ⟨⟨q, by omega⟩, rfl⟩
    rw [← hqF, hτP qF, oK_eq hf hτP hyp hj.le, oK_eq hf hτP hyp hj.le, hτP]
    have h := congrArg (fun g : Equiv.Perm (Fin 8330) => (g qF : ℕ)) (hcomm jj)
    simp only [Equiv.Perm.mul_apply] at h ⊢
    exact h.symm
  · set d := getWI DW (getS rec 2)
    have hd : lettersOK 3 d = true := lettersK_sound hd3
    set k := getS rec 3
    refine ⟨elt d, elt_mem_heAutGroup d, ?_⟩
    have hall : ∀ bw ∈ selB k R5 R7, elt d * elt bw * (elt d)⁻¹ ∈ orbSub y τ := by
      intro bw hbw
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbw
      obtain ⟨hl2, hpts⟩ := basK_sound hb i hi
      rw [List.getD_eq_getElem _ _ hi] at hl2 hpts
      have hb2 : lettersOK 2 (selB k R5 R7)[i] = true := lettersK_sound hl2
      obtain ⟨g, hgm, hgx⟩ := prodO_mem hf hτP hyp (getS rec (4 + i)) p le_rfl
      have hbP : elt (selB k R5 R7)[i] ∈ heP := elt_mem_heP hb2
      have hcP : elt d * elt (selB k R5 R7)[i] * (elt d)⁻¹ ∈ heP :=
        (Subgroup.mem_normalizer_iff.mp (heAutGroup_le_normalizer (elt_mem_heAutGroup d)) _).mp hbP
      have heq : elt d * elt (selB k R5 R7)[i] * (elt d)⁻¹ = g := by
        refine CFSG.KC.WordPts.eq_of_pts baseFaithful_heP hcP (orbSub_le_heP hy hτ hgm)
          fun x hx => Fin.ext ?_
        have hx5 : (x : ℕ) < 5 := by
          simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hx
          omega
        have h1 := hpts x hx5
        have h3 : lettersOK gens3.length d = true := by
          rw [gens3_length]
          exact hd
        have h2 : lettersOK gens3.length (selB k R5 R7)[i] = true :=
          lettersOK_mono (by rw [gens3_length]; norm_num) hb2
        rw [wpIK_eq h3, wpK_eq h2, wpK_eq h3] at h1
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, ← hgx x]
        rfl
      rw [heq]
      exact hgm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · left
      have e : selB k R5 R7 = w5W := by
        rw [hk, ← R5_eq]
        rfl
      rw [e] at hall
      exact hall
    · right
      have e : selB k R5 R7 = w7W := by
        rw [← R7_eq]
        unfold selB
        cases hbk : Nat.beq k 0 with
        | true => exact absurd (Nat.eq_of_beq_eq_true hbk) (by omega)
        | false => rfl
      rw [e] at hall
      exact hall

end CertificateChecks.KernelHe7222

end
