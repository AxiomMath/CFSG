module

public import Certificates.Kernel.Ivk8NormP.J2
public import Certificates.Kernel.Ivk8J2.Final
public import CFSG.Certificates.Kernel.Ivk8NormPKSound
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12NormP
public import Certificates.Certificate5246
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.Ivk8NormP.J2

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  CFSG.KS.Ivk8Cent CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn CertificateChecks.KernelIvk8J2

theorem dom31_5
    {y : Equiv.Perm (Fin 315)}
    (hy : y ∈ j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set (Equiv.Perm (Fin 315))))
    (h5 : orderOf y = 5) :
    (∃ i < J2Q3b.cnt, PR 315 9 (J2Q3b.T i) y) ∨ ∃ i < J2Q3c.cnt, PR 315 9 (J2Q3c.T i) y := by
  obtain ⟨hK', hcard'⟩ := row_cent (i := 2) (by decide) (t := j2CentTbl 31) (cg := cgL 32 4)
    (N := 1920) (by simp [j2Rows]) (by simp [j2Rows]; rfl) (by simp [j2Rows])
  set K := j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set (Equiv.Perm (Fin 315)))
  have hg := gens_of (by norm_num) (by norm_num) kcg.2.2 hK'
  have hE := mulTreeOK_spec (by norm_num) K (gg := fun l => tp 315 (cgL 32 4).toArray[l]!)
    (fun l hl => ⟨(hg l hl).1, (hg l hl).2.2⟩) recC2.2.1
  obtain ⟨k, hk, hyk⟩ := cover_of hE recC2.2.2 (le_of_eq (by rw [hcard', hRec_size, hc2])) y hy
  have hs := Array.all_eq_true.1 sel3 k hk
  have hsel : selOK 315 [3, 5] (hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).1[k] = true := by
    rw [selOK_iff (by norm_num) hyk]
    refine ⟨fun e => ?_, 5, by simp, by rw [← h5]; exact pow_orderOf_eq_one y⟩
    rw [e, orderOf_one] at h5
    exact absurd h5 (by norm_num)
  rw [hsel, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.or_eq_true] at hs
  have hQ := fun r (hr : r < 42) {Q : Array Table} {par lab : Array Nat}
      (hq : conjTreeOK 315 (cgL 32 4).toArray ((cgL 32 4).toArray.map (invT 315)) (j2CentTbl r)
        Q par lab = true) =>
    conjTreeOK_spec K (gg := fun l => tp 315 (cgL 32 4).toArray[l]!) hg (rep_tp (permF hr)) hq
  rcases hs with h1 | h1 | h1
  · have := order_of_queue (hQ 36 (by norm_num) recQ3a.2.1) hyk h1
    rw [h5, ord_rep (by norm_num) (by norm_num) kodd.2.2.2.2.2.1 (by decide) (by norm_num)] at this
    exact absurd this (by norm_num)
  · exact Or.inl (entry_of_queue (hQ 38 (by norm_num) recQ3b.2.1) (canonR (pe_all' q3bE)) hyk h1)
  · exact Or.inr (entry_of_queue (hQ 40 (by norm_num) recQ3c.2.1) (canonR (pe_all' q3cE)) hyk h1)

theorem dom17_5
    {y : Equiv.Perm (Fin 315)}
    (hy : y ∈ j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set (Equiv.Perm (Fin 315))))
    (h5 : orderOf y = 5) :
    (∃ i < J2Q2a.cnt, PR 315 9 (J2Q2a.T i) y) ∨ ∃ i < J2Q2b.cnt, PR 315 9 (J2Q2b.T i) y := by
  obtain ⟨hK', hcard'⟩ := row_cent (i := 1) (by decide) (t := j2CentTbl 17) (cg := cgL 18 5)
    (N := 240) (by simp [j2Rows]) (by simp [j2Rows]; rfl) (by simp [j2Rows])
  set K := j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set (Equiv.Perm (Fin 315)))
  have hg := gens_of (by norm_num) (by norm_num) kcg.2.1 hK'
  have hE := mulTreeOK_spec (by norm_num) K (gg := fun l => tp 315 (cgL 18 5).toArray[l]!)
    (fun l hl => ⟨(hg l hl).1, (hg l hl).2.2⟩) recC1.2.1
  obtain ⟨k, hk, hyk⟩ := cover_of hE recC1.2.2 (le_of_eq (by rw [hcard', hRec_size, hc1])) y hy
  have hs := Array.all_eq_true.1 sel2 k hk
  have hsel : selOK 315 [3, 5] (hRec 315 9 J2C1.cnt J2C1.T J2C1.PL).1[k] = true := by
    rw [selOK_iff (by norm_num) hyk]
    refine ⟨fun e => ?_, 5, by simp, by rw [← h5]; exact pow_orderOf_eq_one y⟩
    rw [e, orderOf_one] at h5
    exact absurd h5 (by norm_num)
  rw [hsel, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.or_eq_true] at hs
  have hQ := fun r (hr : r < 42) {Q : Array Table} {par lab : Array Nat}
      (hq : conjTreeOK 315 (cgL 18 5).toArray ((cgL 18 5).toArray.map (invT 315)) (j2CentTbl r)
        Q par lab = true) =>
    conjTreeOK_spec K (gg := fun l => tp 315 (cgL 18 5).toArray[l]!) hg (rep_tp (permF hr)) hq
  rcases hs with h1 | h1 | h1
  · exact Or.inl (entry_of_queue (hQ 23 (by norm_num) recQ2a.2.1) (canonR (pe_all' q2aE)) hyk h1)
  · exact Or.inr (entry_of_queue (hQ 26 (by norm_num) recQ2b.2.1) (canonR (pe_all' q2bE)) hyk h1)
  · have := order_of_queue (hQ 29 (by norm_num) recQ2c.2.1) hyk h1
    rw [h5, ord_rep (by norm_num) (by norm_num) kodd.2.2.2.2.1 (by decide) (by norm_num)] at this
    exact absurd this (by norm_num)

theorem prs_rep {L : List Nat} {gs : List (Equiv.Perm (Fin 315))}
    (h : List.Forall₂ (PR 315 9) L gs) (hinv : ∀ g ∈ gs, g⁻¹ = g) :
    ∀ x ∈ prs L, ∃ g ∈ {g | g ∈ gs}, PR 315 9 x.1 g ∧ PR 315 9 x.2 g⁻¹ := by
  induction h with
  | nil => simp [prs]
  | @cons a b l l' hab _ ih =>
    intro x hx
    simp only [prs, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨b, List.mem_cons_self .., hab, ?_⟩
      rw [hinv b List.mem_cons_self]
      exact hab
    · obtain ⟨g, hg, h1, h2⟩ := ih (fun g hg => hinv g (List.mem_cons_of_mem _ hg)) x hx
      exact ⟨g, List.mem_cons_of_mem _ hg, h1, h2⟩

theorem wit5_of {c ci : List Nat}
    {cnt : Nat} {T : Nat → Nat} (h : chk5 5 c ci cnt T = true) (hci : pw ci = (pw c)⁻¹)
    (hinv : ∀ g ∈ hsP, g⁻¹ = g) {i : Nat} (hi : i < cnt) {τ : Equiv.Perm (Fin 315)}
    (hT : PR 315 9 (T i) τ) (hτ : orderOf τ = 5) :
    ∃ g ∈ hsP, g ∉ normalizer (zpowers (pw c * τ * (pw c)⁻¹) : Set (Equiv.Perm (Fin 315))) := by
  unfold chk5 wH at h
  rw [withH_eq] at h
  simp only [PF.strictB_eqP] at h
  have hci' := pr_w ci
  rw [hci] at hci'
  exact chkPK_sound J2Cn.hn (by norm_num) (prs_rep hs_pr hinv) (pr_w c) hci' h hi hT hτ

theorem prime_dvd_1920' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 1920) : p = 3 ∨ p = 5 := by
  have e : (1920 : ℕ) = 2 ^ 7 * (3 * 5) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

theorem j2_noP
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 315)), P ≤ j2P → W ≤ j2P → Nat.card P = 2 ^ 7 →
      IsPGroup p W → P ≤ normalizer (W : Set (Equiv.Perm (Fin 315))) → W = ⊥ := by
  by_cases hp3 : p = 3
  · subst hp3
    exact Certificates.certificate5246
  obtain ⟨hA2, hB2, hC2, hAB, hAC, hBC, hC1, hAB1, hCAB⟩ := hfacts
  obtain ⟨⟨e1i, e1⟩, ⟨e2i, e2⟩, ⟨e3i, e3⟩⟩ := efacts
  set A := pw wA
  set B := pw wB
  set C := pw wC
  set H := closure ({A, B, C} : Set (Equiv.Perm (Fin 315)))
  have hgens : ∀ s ∈ ({A, B, C} : Set (Equiv.Perm (Fin 315))), s ∈ j2P := by
    rintro s (rfl | rfl | rfl)
    · exact pw_mem wA
    · exact pw_mem wB
    · exact pw_mem wC
  have hHP : H ≤ j2P := (closure_le _).2 hgens
  have hcomm1 : ∀ x ∈ H, ∀ s ∈ ({A, B, C} : Set (Equiv.Perm (Fin 315))), Commute x s := by
    intro x hx
    induction hx using closure_induction with
    | mem y hy =>
      rintro s hs
      rcases hy with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl
      · exact Commute.refl A
      · exact hAB
      · exact hAC
      · exact hAB.symm
      · exact Commute.refl B
      · exact hBC
      · exact hAC.symm
      · exact hBC.symm
      · exact Commute.refl C
    | one => exact fun s _ => Commute.one_left s
    | mul y z _ _ hy hz => exact fun s hs => (hy s hs).mul_left (hz s hs)
    | inv y _ hy => exact fun s hs => (hy s hs).inv_left
  have hcomm : ∀ x ∈ H, ∀ y ∈ H, Commute x y := by
    intro x hx y hy
    induction hy using closure_induction with
    | mem z hz => exact hcomm1 x hx z hz
    | one => exact Commute.one_right x
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  have hsq : ∀ x ∈ H, x * x = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl | rfl
      · exact hA2
      · exact hB2
      · exact hC2
    | one => exact mul_one 1
    | mul y z hy hz ihy ihz =>
      calc y * z * (y * z) = y * y * (z * z) := by
            rw [mul_assoc, ← mul_assoc z y z, ← (hcomm y hy z hz).eq]
            group
        _ = 1 := by rw [ihy, ihz, mul_one]
    | inv y _ hy => rw [← mul_inv_rev, hy, inv_one]
  have hH2 : IsPGroup 2 H := fun x => ⟨1, by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_one, pow_two]
    exact hsq x x.2⟩
  have hmemA : A ∈ H := subset_closure (by simp)
  have hmemB : B ∈ H := subset_closure (by simp)
  have hmemC : C ∈ H := subset_closure (by simp)
  have hmemAB : A * B ∈ H := mul_mem hmemA hmemB
  have hsH : ∀ a ∈ hsP, a ∈ H := by
    intro a ha
    simp only [hsP, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hmemA
    · exact hmemB
    · exact hmemAB
    · exact hmemC
    · exact mul_mem hmemA hmemC
    · exact mul_mem hmemB hmemC
    · exact mul_mem hmemAB hmemC
  have hinv : ∀ g ∈ hsP, g⁻¹ = g := fun g hg => inv_eq_of_mul_eq_one_right (hsq g (hsH g hg))
  set t17 := tp 315 (j2CentTbl 17)
  set t31 := tp 315 (j2CentTbl 31)
  set K17 := j2P ⊓ centralizer ({t17} : Set (Equiv.Perm (Fin 315)))
  set K31 := j2P ⊓ centralizer ({t31} : Set (Equiv.Perm (Fin 315)))
  obtain ⟨-, hc17⟩ := row_cent (i := 1) (by decide) (t := j2CentTbl 17) (cg := cgL 18 5)
    (N := 240) (by simp [j2Rows]) (by simp [j2Rows]; rfl) (by simp [j2Rows])
  obtain ⟨-, hc31⟩ := row_cent (i := 2) (by decide) (t := j2CentTbl 31) (cg := cgL 32 4)
    (N := 1920) (by simp [j2Rows]) (by simp [j2Rows]; rfl) (by simp [j2Rows])
  set ds : List (Equiv.Perm (Fin 315) × Equiv.Perm (Fin 315) × Subgroup (Equiv.Perm (Fin 315))) :=
    [(pw c1, t17, K17), (pw c2, t31, K31), (pw c3, t17, K17)] with hds
  have hdvd : ∀ d ∈ ds, Nat.card d.2.2 ∣ 1920 := by
    intro d hd
    simp only [hds, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · rw [hc17]
      norm_num
    · rw [hc31]
    · rw [hc17]
      norm_num
  have hK : ∀ d ∈ ds, ∀ x ∈ j2P, x * d.2.1 = d.2.1 * x → x ∈ d.2.2 := by
    intro d hd x hx hxr
    simp only [hds, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      exact mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxr⟩
  have hpK : ∀ d ∈ ds, ¬ p ^ 2 ∣ Nat.card d.2.2 := by
    intro d hd h
    have h1 := h.trans (hdvd d hd)
    rcases prime_dvd_1920' hp hp2 ((dvd_pow_self p two_ne_zero).trans h1) with rfl | rfl <;>
      norm_num at h1
  have hcs : ∀ d ∈ ds, d.1 ∈ j2P := by
    intro d hd
    simp only [hds, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact pw_mem c1
    · exact pw_mem c2
    · exact pw_mem c3
  have hcov : ∀ e ∈ [C, A * B, C * (A * B)], ∃ d ∈ ds, d.1 * d.2.1 * d.1⁻¹ = e := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨(pw c1, t17, K17), by simp [hds], e1⟩
    · exact ⟨(pw c2, t31, K31), by simp [hds], e2⟩
    · refine ⟨(pw c3, t17, K17), by simp [hds], ?_⟩
      rw [e3]
      exact (hcomm _ hmemAB _ hmemC).eq
  have hN : ∀ d ∈ ds, ∀ y ∈ d.2.2, orderOf y = p →
      ∃ h ∈ H, h ∉ normalizer (zpowers (d.1 * y * d.1⁻¹) : Set (Equiv.Perm (Fin 315))) := by
    intro d hd y hy hyo
    have hp5 : p = 5 := by
      rcases prime_dvd_1920' hp hp2 (by
          rw [← hyo, ← Subgroup.orderOf_mk y hy]
          exact (_root_.orderOf_dvd_natCard _).trans (hdvd d hd)) with h | h
      · exact absurd h hp3
      · exact h
    subst hp5
    have lift : ∀ {z : Equiv.Perm (Fin 315)}, (∃ g ∈ hsP, g ∉ normalizer
        (zpowers z : Set (Equiv.Perm (Fin 315)))) →
        ∃ h ∈ H, h ∉ normalizer (zpowers z : Set (Equiv.Perm (Fin 315))) := by
      rintro z ⟨g, hg, hgN⟩
      exact ⟨g, hsH g hg, hgN⟩
    simp only [hds, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · rcases dom17_5 hy hyo with ⟨i, hi, hT⟩ | ⟨i, hi, hT⟩
      · exact lift (wit5_of ch5253_j2_q2a1 e1i hinv hi hT hyo)
      · exact lift (wit5_of ch5253_j2_q2b1 e1i hinv hi hT hyo)
    · rcases dom31_5 hy hyo with ⟨i, hi, hT⟩ | ⟨i, hi, hT⟩
      · exact lift (wit5_of ch5253_j2_q3b e2i hinv hi hT hyo)
      · exact lift (wit5_of ch5253_j2_q3c e2i hinv hi hT hyo)
    · rcases dom17_5 hy hyo with ⟨i, hi, hT⟩ | ⟨i, hi, hT⟩
      · exact lift (wit5_of ch5253_j2_q2a3 e3i hinv hi hT hyo)
      · exact lift (wit5_of ch5253_j2_q2b3 e3i hinv hi hT hyo)
  have hS₀ : ¬ 2 ^ (7 + 1) ∣ Nat.card j2P := by
    rw [card_j2P]
    norm_num
  exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.noP_of_cents le_rfl hp hp2 hmemC hmemAB hC2
    (hsq _ hmemAB) (hcomm _ hmemC _ hmemAB).eq hC1 hAB1 hCAB hH2 hHP
    (fun h hh => ⟨(hcomm _ hh _ hmemC).eq, (hcomm _ hh _ hmemAB).eq⟩) hK hpK hcs hcov hN hS₀

end CFSG.KS.Ivk8NormP.J2

end
