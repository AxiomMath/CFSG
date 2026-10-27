module

public import Certificates.Kernel.He7222.GlueCls
public import Certificates.Kernel.He7222.ConjK
public import CFSG.Quasithin.Vol2.KGFactC31Orb
public import CFSG.Certificates.Kernel.He7222.FixSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.OrbRow.LevelSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223
  CertificateChecks.KernelSchreierFam.He725

@[expose] def HConcl (τ y : Equiv.Perm (Fin 8330)) : Prop :=
  y * τ * y⁻¹ ≠ τ → (∃ e ∈ [25, 343, 17], y ^ e = 1) →
    (∀ j : ℕ, τ * (y ^ j * τ * (y ^ j)⁻¹) = y ^ j * τ * (y ^ j)⁻¹ * τ) →
    ∃ d ∈ heAutGroup, (∀ bw ∈ w5W, d * elt bw * d⁻¹ ∈ orbSub y τ) ∨
      (∀ bw ∈ w7W, d * elt bw * d⁻¹ ∈ orbSub y τ)

theorem hconcl_of_conj {τ c y : Equiv.Perm (Fin 8330)} (hc : c ∈ heP) (hcτ : c * τ = τ * c)
    (h : HConcl τ (c⁻¹ * y * c)) : HConcl τ y := by
  intro hmove he hcomm
  have htc : τ = c * τ * c⁻¹ := by rw [hcτ, mul_inv_cancel_right]
  have hpow : ∀ j : ℕ, (c⁻¹ * y * c) ^ j = c⁻¹ * y ^ j * c := fun j => by
    rw [show c⁻¹ * y * c = c⁻¹ * y * c⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
  have hmove' : c⁻¹ * y * c * τ * (c⁻¹ * y * c)⁻¹ ≠ τ := by
    intro h1
    apply hmove
    calc y * τ * y⁻¹ = y * (c * τ * c⁻¹) * y⁻¹ := by rw [← htc]
      _ = c * (c⁻¹ * y * c * τ * (c⁻¹ * y * c)⁻¹) * c⁻¹ := by group
      _ = τ := by rw [h1, ← htc]
  have he' : ∃ e ∈ [25, 343, 17], (c⁻¹ * y * c) ^ e = 1 := by
    obtain ⟨e, hes, hye⟩ := he
    exact ⟨e, hes, by rw [hpow, hye, mul_one, inv_mul_cancel]⟩
  have hcomm' : ∀ j : ℕ, τ * ((c⁻¹ * y * c) ^ j * τ * ((c⁻¹ * y * c) ^ j)⁻¹) =
      (c⁻¹ * y * c) ^ j * τ * ((c⁻¹ * y * c) ^ j)⁻¹ * τ := by
    intro j
    have h1 := hcomm j
    rw [hpow]
    have e1 : τ * (c⁻¹ * y ^ j * c * τ * (c⁻¹ * y ^ j * c)⁻¹) = c⁻¹ * ((c * τ * c⁻¹) *
        (y ^ j * (c * τ * c⁻¹) * (y ^ j)⁻¹)) * c := by group
    have e2 : c⁻¹ * y ^ j * c * τ * (c⁻¹ * y ^ j * c)⁻¹ * τ = c⁻¹ * (y ^ j * (c * τ * c⁻¹) *
        (y ^ j)⁻¹ * (c * τ * c⁻¹)) * c := by group
    rw [e1, e2, ← htc, h1]
  obtain ⟨d, hd, hm⟩ := h hmove' he' hcomm'
  have hU : (orbSub (c⁻¹ * y * c) τ).map (MulAut.conj c).toMonoidHom = orbSub y τ := by
    rw [orbSub_map]
    congr 1
    · change c * (c⁻¹ * y * c) * c⁻¹ = y
      group
    · exact htc.symm
  have hmap : ∀ g ∈ orbSub (c⁻¹ * y * c) τ, c * g * c⁻¹ ∈ orbSub y τ := fun g hg => by
    rw [← hU]
    exact ⟨g, hg, rfl⟩
  have e : ∀ bw, c * (d * elt bw * d⁻¹) * c⁻¹ = c * d * elt bw * (c * d)⁻¹ := fun bw => by group
  refine ⟨c * d, heAutGroup.mul_mem (heP_le_heAutGroup hc) hd, ?_⟩
  rcases hm with hm | hm
  · exact Or.inl fun bw hbw => by rw [← e]; exact hmap _ (hm bw hbw)
  · exact Or.inr fun bw hbw => by rw [← e]; exact hmap _ (hm bw hbw)

theorem hconcl_of_entry {τ : Equiv.Perm (Fin 8330)} {Hs : ℕ → Equiv.Perm (Fin 8330)} {J : ℕ}
    (hent : ∀ y ∈ heP, y * τ * y⁻¹ ≠ τ → τ * (y * τ * y⁻¹) = y * τ * y⁻¹ * τ →
      ∃ c ∈ centralizerIn heP τ, ∃ j < J, ∃ z ∈ centralizerIn heP τ, y = c * Hs j * z)
    (hscan : ∀ j < J, ∀ z ∈ centralizerIn heP τ, HConcl τ (Hs j * z)) :
    ∀ y ∈ heP, HConcl τ y := by
  intro y hy hmove he hcomm
  have h1 := hcomm 1
  simp only [pow_one] at h1
  obtain ⟨c, hc, j, hj, z, hz, rfl⟩ := hent y hy hmove h1
  obtain ⟨hcP, hcτ⟩ := mem_centralizerIn.1 hc
  refine hconcl_of_conj hcP hcτ ?_ hmove he hcomm
  have e : c⁻¹ * (c * Hs j * z) * c = Hs j * (z * c) := by group
  rw [e]
  exact hscan j hj _ ((centralizerIn heP τ).mul_mem hz hc)

theorem not_rep_of_conj {τ y c r : Equiv.Perm (Fin 8330)} (hr : ∀ g : Equiv.Perm (Fin 8330),
    r ≠ g * τ * g⁻¹) (hs : y * τ * y⁻¹ = c * r * c⁻¹) : False := by
  apply hr (c⁻¹ * y)
  calc r = c⁻¹ * (c * r * c⁻¹) * c := by group
    _ = c⁻¹ * (y * τ * y⁻¹) * c := by rw [hs]
    _ = c⁻¹ * y * τ * (c⁻¹ * y)⁻¹ := by group

theorem coset_of_conj {τ y c h s : Equiv.Perm (Fin 8330)} (hy : y ∈ heP)
    (hc : c ∈ centralizerIn heP τ) (hh : h ∈ heP) (hhs : h * τ = s * h)
    (hs : y * τ * y⁻¹ = c * s * c⁻¹) :
    ∃ z ∈ centralizerIn heP τ, y = c * h * z := by
  have hcP := (mem_centralizerIn.1 hc).1
  refine ⟨(c * h)⁻¹ * y, mem_centralizerIn.2 ⟨heP.mul_mem (heP.inv_mem (heP.mul_mem hcP hh)) hy,
    ?_⟩, by group⟩
  have hs' : s = h * τ * h⁻¹ := by rw [hhs, mul_inv_cancel_right]
  have e : y * τ = c * h * τ * h⁻¹ * c⁻¹ * y := by
    calc y * τ = y * τ * y⁻¹ * y := by group
      _ = c * s * c⁻¹ * y := by rw [hs]
      _ = c * h * τ * h⁻¹ * c⁻¹ * y := by rw [hs']; group
  calc (c * h)⁻¹ * y * τ = (c * h)⁻¹ * (y * τ) := by group
    _ = (c * h)⁻¹ * (c * h * τ * h⁻¹ * c⁻¹ * y) := by rw [e]
    _ = τ * ((c * h)⁻¹ * y) := by group

@[expose] noncomputable def hP (j : ℕ) : Equiv.Perm (Fin 8330) := elt (HW.getD j [])

theorem ch7222hw : (lettersOK 2 (HW.getD 0 []) && lettersOK 2 (HW.getD 1 []) &&
    lettersOK 2 (HW.getD 2 []) && lettersOK 2 (HW.getD 3 []) && lettersOK 2 (HW.getD 4 []) &&
    lettersOK 2 (HW.getD 5 []) && lettersOK 2 (HW.getD 6 []) && lettersOK 2 (HW.getD 7 [])) =
    true := by
  decide +kernel

theorem hw_letters : ∀ j < 8, lettersOK 2 (HW.getD j []) = true := by
  have h := ch7222hw
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  intro j hj
  match j, hj with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7

theorem hP_mem {j : ℕ} (hj : j < 8) :
    hP j ∈ heP :=
  elt_mem_heP (hw_letters j hj)

theorem hK_all : ∀ j < 8, hK j = true
  | 0, _ => ch7222h0
  | 1, _ => ch7222h1
  | 2, _ => ch7222h2
  | 3, _ => ch7222h3
  | 4, _ => ch7222h4
  | 5, _ => ch7222h5
  | 6, _ => ch7222h6
  | 7, _ => ch7222h7
  | _ + 8, h => absurd h (by omega)

theorem prep_hP {j : ℕ}
    (hj : j < 8) : PRep 8330 14 (getS scH j) (hP j) := by
  have hrep : Rep 8330 (unpack 8330 14 (getS scH j)) (hP j) := by
    rw [← (wordEqK_sound gA_bind kPLU (hK_all j hj)).1]
    exact rep_wA (lettersOK_mono (by norm_num) (hw_letters j hj))
  exact prep_of_rep hrep

theorem conj_of_cjK {h t s : ℕ} {hg τ sg : Equiv.Perm (Fin 8330)} (hc : cjK h t s = true)
    (hh : PRep 8330 14 h hg) (ht : PRep 8330 14 t τ) (hs : PRep 8330 14 s sg) :
    hg * τ = sg * hg := by
  unfold cjK at hc
  rw [bAnd_iff] at hc
  have he := Nat.eq_of_beq_eq_true hc.2
  have h1 := prep_pcomp (by norm_num) hh ht
  have h2 := prep_pcomp (by norm_num) hs hh
  rw [he] at h1
  exact prep_unique h1 h2

theorem a0_hrep :
    ∀ t < a0Ts.length, ∀ j < (a0Ts.getD t []).length,
      PRep 8330 14 ((a0Ts.getD t []).getD j 0) (rec0 t j) := fun t ht j hj =>
  (a0_cent_chain.1 t ht j hj).2.1

theorem prep_rep0
    {r : ℕ}
    (ht : tupOK a0Ts (getLs a0RT r) = true) :
    PRep 8330 14 (rep0 r) (rep0P r) ∧ rep0P r ∈ centralizerIn heP (heGenPerm 0) := by
  refine ⟨tupK_rep (by norm_num) (by norm_num) rec0 ht a0_hrep, ?_⟩
  obtain ⟨-, hixb⟩ := tupOK_spec ht
  refine Subgroup.list_prod_mem (K := centralizerIn heP (heGenPerm 0)) fun g hg => ?_
  simp only [tupL, List.mem_map, List.mem_range] at hg
  obtain ⟨t, ht', rfl⟩ := hg
  exact (a0_cent_chain.1 t ht' _ (hixb t ht')).1

theorem ch7222srep : (Nat.beq (getS a0SRep 0) 0 && Nat.beq (getS a0SRep 1) 1 &&
    Nat.beq (getS a0SRep 2) 4 && Nat.beq (getS t1SRep 0) 1 && Nat.beq (getS t1SRep 1) 2 &&
    Nat.beq (getS t1SRep 2) 3 && Nat.beq (getS t1SRep 3) 5 && Nat.beq (getS t1SRep 4) 6) =
    true := by
  quickRfl

theorem a0_scan_entry :
    ∀ y ∈ heP, y * heGenPerm 0 * y⁻¹ ≠ heGenPerm 0 →
      heGenPerm 0 * (y * heGenPerm 0 * y⁻¹) = y * heGenPerm 0 * y⁻¹ * heGenPerm 0 →
      ∃ c ∈ centralizerIn heP (heGenPerm 0), ∃ j < 3, ∃ z ∈ centralizerIn heP (heGenPerm 0),
        y = c * hP j * z := by
  intro y hy hmove hcm
  have hτ := heGenPerm_mem (by norm_num : (0 : ℕ) < 2)
  have hτ2 : heGenPerm 0 * heGenPerm 0 = 1 := by
    rw [← sq, ← orderOf_heA0]
    exact pow_orderOf_eq_one _
  have hx : y * heGenPerm 0 * y⁻¹ ∈ centralizerIn heP (heGenPerm 0) :=
    mem_centralizerIn.2 ⟨heP.mul_mem (heP.mul_mem hy hτ) (heP.inv_mem hy), hcm.symm⟩
  have hx2 : y * heGenPerm 0 * y⁻¹ * (y * heGenPerm 0 * y⁻¹) = 1 := by
    calc y * heGenPerm 0 * y⁻¹ * (y * heGenPerm 0 * y⁻¹) = y * (heGenPerm 0 * heGenPerm 0) * y⁻¹ :=
          by group
      _ = 1 := by rw [hτ2, mul_one, mul_inv_cancel]
  have hx1 : y * heGenPerm 0 * y⁻¹ ≠ 1 := fun h1 => heA0_ne_one (by
    calc heGenPerm 0 = y⁻¹ * (y * heGenPerm 0 * y⁻¹) * y := by group
      _ = 1 := by rw [h1, mul_one, inv_mul_cancel])
  obtain ⟨cl, hcl, c, hc, hs⟩ := a0_inv_class _ hx hx2 hx1 hmove
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, r4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hrt
  have hsr := ch7222srep
  simp only [Bool.and_eq_true] at hsr
  obtain ⟨⟨⟨⟨⟨⟨⟨s0, s1⟩, s2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hsr
  have scan : ∀ j < 3, ∀ r, getS a0SRep j = r → tupOK a0Ts (getLs a0RT r) = true →
      cjK (getS scH j) (HG.F 0) (rep0 (getS a0SRep j)) = true → rep0P cl = rep0P r →
      ∃ c ∈ centralizerIn heP (heGenPerm 0), ∃ j < 3, ∃ z ∈ centralizerIn heP (heGenPerm 0),
        y = c * hP j * z := by
    intro j hj r hjr ht hcj hr
    rw [hjr] at hcj
    have hhs := conj_of_cjK hcj (prep_hP (by omega)) prep_a0 (prep_rep0 ht).1
    rw [hr] at hs
    obtain ⟨z, hz, hyz⟩ := coset_of_conj hy hc (hP_mem (by omega)) hhs hs
    exact ⟨c, hc, j, hj, z, hz, hyz⟩
  match cl, hcl with
  | 0, _ => exact scan 0 (by norm_num) 0 (Nat.eq_of_beq_eq_true s0) r0 ch7222cj0 rfl
  | 1, _ => exact scan 1 (by norm_num) 1 (Nat.eq_of_beq_eq_true s1) r1 ch7222cj1 rfl
  | 4, _ => exact scan 2 (by norm_num) 4 (Nat.eq_of_beq_eq_true s2) r4 ch7222cj2 rfl
  | 2, _ => exact (not_rep_of_conj (not_conj_of_fixNeK ch7222fix0 (prep_rep0 r2).1 prep_a0)
      hs).elim
  | 3, _ => exact (not_rep_of_conj (not_conj_of_fixNeK ch7222fix1 (prep_rep0 r3).1 prep_a0)
      hs).elim

theorem t1_hrep :
    ∀ t < t1Ts.length, ∀ j < (t1Ts.getD t []).length,
      PRep 8330 14 ((t1Ts.getD t []).getD j 0) (rec1 t j) := fun t ht j hj =>
  (t1_cent_chain.1 t ht j hj).2.1

theorem prep_rep1
    {r : ℕ} (ht : tupOK t1Ts (getLs t1RT r) = true) :
    PRep 8330 14 (rep1 r) (rep1P r) ∧ rep1P r ∈ centralizerIn heP heT1P := by
  refine ⟨tupK_rep (by norm_num) (by norm_num) rec1 ht t1_hrep, ?_⟩
  obtain ⟨-, hixb⟩ := tupOK_spec ht
  refine Subgroup.list_prod_mem (K := centralizerIn heP heT1P) fun g hg => ?_
  simp only [tupL, List.mem_map, List.mem_range] at hg
  obtain ⟨t, ht', rfl⟩ := hg
  exact (t1_cent_chain.1 t ht' _ (hixb t ht')).1

theorem t1_scan_entry :
    ∀ y ∈ heP, y * heT1P * y⁻¹ ≠ heT1P →
      heT1P * (y * heT1P * y⁻¹) = y * heT1P * y⁻¹ * heT1P →
      ∃ c ∈ centralizerIn heP heT1P, ∃ j < 5, ∃ z ∈ centralizerIn heP heT1P,
        y = c * hP (3 + j) * z := by
  intro y hy hmove hcm
  have hτ := heT1P_mem
  have hτ2 : heT1P * heT1P = 1 := by
    rw [← sq, ← orderOf_heT1P]
    exact pow_orderOf_eq_one _
  have hx : y * heT1P * y⁻¹ ∈ centralizerIn heP heT1P :=
    mem_centralizerIn.2 ⟨heP.mul_mem (heP.mul_mem hy hτ) (heP.inv_mem hy), hcm.symm⟩
  have hx2 : y * heT1P * y⁻¹ * (y * heT1P * y⁻¹) = 1 := by
    calc y * heT1P * y⁻¹ * (y * heT1P * y⁻¹) = y * (heT1P * heT1P) * y⁻¹ := by group
      _ = 1 := by rw [hτ2, mul_one, mul_inv_cancel]
  have hx1 : y * heT1P * y⁻¹ ≠ 1 := fun h1 => heT1P_ne_one (by
    calc heT1P = y⁻¹ * (y * heT1P * y⁻¹) * y := by group
      _ = 1 := by rw [h1, mul_one, inv_mul_cancel])
  obtain ⟨cl, hcl, c, hc, hs⟩ := t1_inv_class _ hx hx2 hx1 hmove
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, r0⟩, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩ := hrt
  have hsr := ch7222srep
  simp only [Bool.and_eq_true] at hsr
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, s0⟩, s1⟩, s2⟩, s3⟩, s4⟩ := hsr
  have scan : ∀ j < 5, ∀ r, getS t1SRep j = r → tupOK t1Ts (getLs t1RT r) = true →
      cjK (getS scH (3 + j)) PT1 (rep1 (getS t1SRep j)) = true → rep1P cl = rep1P r →
      ∃ c ∈ centralizerIn heP heT1P, ∃ j < 5, ∃ z ∈ centralizerIn heP heT1P,
        y = c * hP (3 + j) * z := by
    intro j hj r hjr ht hcj hr
    rw [hjr] at hcj
    have hhs := conj_of_cjK hcj (prep_hP (by omega)) prep_t1 (prep_rep1 ht).1
    rw [hr] at hs
    obtain ⟨z, hz, hyz⟩ := coset_of_conj hy hc (hP_mem (by omega)) hhs hs
    exact ⟨c, hc, j, hj, z, hz, hyz⟩
  match cl, hcl with
  | 1, _ => exact scan 0 (by norm_num) 1 (Nat.eq_of_beq_eq_true s0) r1 ch7222cj3 rfl
  | 2, _ => exact scan 1 (by norm_num) 2 (Nat.eq_of_beq_eq_true s1) r2 ch7222cj4 rfl
  | 3, _ => exact scan 2 (by norm_num) 3 (Nat.eq_of_beq_eq_true s2) r3 ch7222cj5 rfl
  | 5, _ => exact scan 3 (by norm_num) 5 (Nat.eq_of_beq_eq_true s3) r5 ch7222cj6 rfl
  | 6, _ => exact scan 4 (by norm_num) 6 (Nat.eq_of_beq_eq_true s4) r6 ch7222cj7 rfl
  | 0, _ => exact (not_rep_of_conj (not_conj_of_fixNeK ch7222fix2 (prep_rep1 r0).1 prep_t1)
      hs).elim
  | 4, _ => exact (not_rep_of_conj (not_conj_of_fixNeK ch7222fix3 (prep_rep1 r4).1 prep_t1)
      hs).elim

end CertificateChecks.KernelHe7222

end
