module

public import Certificates.Kernel.Misc.Sp6Transv.FactsQ
import CFSG.Certificates.Kernel.Misc.PermClosProof

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6Transv.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Spec
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6Transv

variable {z : Fin 3 → H6} {t s f0 f2 : H6} {q : Fin 5 → H6}

theorem pkMat_enc6 (h : H6) : pkMat 6 (enc6 h) = mat6 h := by
  rw [enc6, ← dec6_eq_pkMat (canon6_code6 _), dec6_code6]

theorem pkMat_inv {g : H6} {X : ℕ} (h : MULF (enc6 g) X = ONE) : pkMat 6 X = mat6 g⁻¹ := by
  have h1 : mat6 g * pkMat 6 X = 1 := by
    rw [← pkMat_enc6, ← pkMat_MULF, h, ← enc_one, pkMat_enc6, map_one]
  calc pkMat 6 X = (mat6 g⁻¹ * mat6 g) * pkMat 6 X := by
        rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
    _ = mat6 g⁻¹ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conjF_enc {g x : H6} {X : ℕ} (h : MULF (enc6 g) X = ONE) :
    conjF (enc6 g) X (enc6 x) = enc6 (g * x * g⁻¹) := by
  refine pkMat_inj (MULF_lt _ _) (enc6_lt _) ?_
  rw [conjF, pkMat_MULF, pkMat_MULF, pkMat_inv h, pkMat_enc6, pkMat_enc6, pkMat_enc6, map_mul,
    map_mul]

theorem Hyp.le_of_card (H : Hyp z t s f0 f2 q) {R X : Subgroup H6}
    (hR : R ≤ Subgroup.centralizer ({s} : Set H6)) (h2 : IsPGroup 2 R)
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6))
    (hX : X ≤ Subgroup.centralizer ({s} : Set H6)) (hXc : Nat.card X = 512) : R ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 : IsPGroup 2 X := IsPGroup.of_card (n := 9) (by rw [hXc]; norm_num)
  have hsup : IsPGroup 2 (X ⊔ R : Subgroup H6) :=
    IsPGroup.to_sup_of_normal_right' hX2 h2 (hX.trans hN)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(X ⊔ R))).mp hsup
  have hd : 2 ^ k ∣ 512 * 45 := by
    rw [← hk, show 512 * 45 = Nat.card (Subgroup.centralizer ({s} : Set H6)) by
      rw [H.card_cen]]
    exact Subgroup.card_dvd_of_le (sup_le hX hR)
  have hk' : 2 ^ k ∣ 512 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 45)).dvd_of_dvd_mul_right hd
  have hle : Nat.card (X ⊔ R : Subgroup H6) ≤ Nat.card X := by
    rw [hk, hXc]
    exact Nat.le_of_dvd (by norm_num) hk'
  have heq : X = X ⊔ R := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  rw [heq]
  exact le_sup_right

theorem inter_at (k : ℕ) (hk : k < 512) :
    interAt E S EQ NB (MULF (KS 5) (KS 5)) (MULF (KS 7) (KS 7)) k = true := by
  have h := forall_of_chunks 256 2 _ (fun c hc => IK.all c hc) k (by omega)
  exact h

theorem Hyp.le_Q (H : Hyp z t s f0 f2 q) {R : Subgroup H6}
    (hR : R ≤ Subgroup.centralizer ({s} : Set H6)) (h2 : IsPGroup 2 R)
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6)) :
    R ≤ Subgroup.closure (Set.range q) := by
  set c := cs0 * cs0 with hc
  have hcC : c ∈ Subgroup.centralizer ({s} : Set H6) := mul_mem H.cs0_mem H.cs0_mem
  have hT := H.le_of_card hR h2 hN H.T1_le T1_facts.2.1
  have hT' := H.le_of_card hR h2 hN (X := T1.map (MulAut.conj c).toMonoidHom)
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hcC (H.T1_le hy)) (inv_mem hcC))
    (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, T1_facts.2.1])
  intro x hx
  obtain ⟨k, hk, ek⟩ := T1_facts.2.2 x (hT hx)
  obtain ⟨y, hy, hyx⟩ := hT' hx
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  obtain ⟨k', hk', ek'⟩ := T1_facts.2.2 y hy
  have h := inter_at k hk
  simp only [interAt, letB_eq] at h
  cases hb : Nat.ble 1048576 (NB k)
  · rw [hb] at h
    obtain ⟨hr, h⟩ := andB_eq_true h
    obtain ⟨hlo, hhi⟩ := andB_eq_true h
    have hr' : NB k ≤ 512 := Nat.ble_eq.mp hr
    have hy' : MULF (MULF (MULF (KS 7) (KS 7)) (E k)) (MULF (KS 5) (KS 5)) = enc6 y := by
      rw [← ek, ← enc_cs0.1, ← enc_cs0.2, ← emul, ← emul, ← emul, ← emul, ← hyx, hc]
      exact congrArg enc6 (by group)
    have hne := not_mem_of_gap
      (y := MULF (MULF (MULF (KS 7) (KS 7)) (E k)) (MULF (KS 5) (KS 5))) sort_T1 hr'
      (fun h0 => by
        have h' := Nat.blt_eq.mp (impB_eq_true hlo (Nat.blt_eq.mpr h0))
        rwa [Nat.pred_eq_sub_one] at h')
      (fun h1 => Nat.blt_eq.mp (impB_eq_true hhi (Nat.blt_eq.mpr h1))) k' hk'
    exact absurd (ek'.symm.trans hy'.symm) hne
  · rw [hb] at h
    obtain ⟨hj, he⟩ := andB_eq_true h
    obtain ⟨g, hg, eg⟩ := H.Q_facts.1 _ (Nat.blt_eq.mp hj)
    rw [Nat.eq_of_beq_eq_true he, ← ek] at eg
    rwa [← eq_of_enc eg]

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem orB_true {a b : Bool} (h : CFSG.KC.Ord.orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem sp_parts :
    (∀ k < 12, treeAt MULF ONE (fun l => KS (Nat.add 5 l)) 2 K KP k = true) ∧
    (∀ k < 12, invAt K KI k = true) ∧ (∀ m < 30, spanAt EQ SQ SKI K KI SE SPP SS m = true) ∧
    coverQ EQ SQ (KS 0) = true := by
  have h : spB 0 = true := PK.all 0 (by norm_num)
  unfold spB at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h4⟩ := andB_eq_true h
  have r : ∀ {n : ℕ} {f : ℕ → Bool}, allR 0 n f = true → ∀ i < n, f i = true :=
    fun h i hi => (allR_iff _ _ _).1 h i (Nat.zero_le _) (by omega)
  exact ⟨r h1, r h2, r h3, h4⟩

theorem tree_mem (gens : List H6) {G : ℕ → ℕ} (hG : ∀ j < gens.length, G j = enc6 (gens.getD j 1))
    {N : ℕ} {E PA : ℕ → ℕ} (ht : ∀ k < N, treeAt MULF ONE G gens.length E PA k = true) :
    ∀ k < N, ∃ g ∈ Subgroup.closure {g | g ∈ gens}, enc6 g = E k := by
  have hmem : ∀ j < gens.length, gens.getD j 1 ∈ Subgroup.closure {g | g ∈ gens} := fun j hj =>
    Subgroup.subset_closure (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact List.getElem_mem hj)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero =>
      have h : Nat.beq (E 0) ONE = true := ht 0 hk
      exact ⟨1, one_mem _, by rw [enc_one]; exact (Nat.eq_of_beq_eq_true h).symm⟩
    | succ k =>
      have h := ht (k + 1) hk
      simp only [treeAt, letB_eq] at h
      obtain ⟨hp, h⟩ := andB_eq_true h
      obtain ⟨hl, he⟩ := andB_eq_true h
      obtain ⟨g, hg, hge⟩ := ih _ (Nat.blt_eq.mp hp) (by have := Nat.blt_eq.mp hp; omega)
      refine ⟨g * gens.getD _ 1, mul_mem hg (hmem _ (Nat.blt_eq.mp hl)), ?_⟩
      rw [emul, hge, ← hG _ (Nat.blt_eq.mp hl)]
      exact (Nat.eq_of_beq_eq_true he).symm

theorem Hyp.K_mem (H : Hyp z t s f0 f2 q) :
    ∀ k < 12, ∃ g ∈ Subgroup.centralizer ({s} : Set H6), enc6 g = K k ∧
      MULF (enc6 g) (KI k) = ONE ∧ KI k < 2 ^ 36 := by
  have hG : ∀ j < [cs0, cs1].length, KS (Nat.add 5 j) = enc6 ([cs0, cs1].getD j 1) := by
    intro j hj
    have hj' : j < 2 := by simpa using hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact enc_cs0.1.symm
    · exact enc_cs1.1.symm
  have hle : Subgroup.closure {g | g ∈ [cs0, cs1]} ≤ Subgroup.centralizer ({s} : Set H6) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
    rcases hg with rfl | rfl
    · exact H.cs0_mem
    · exact H.cs1_mem
  intro k hk
  obtain ⟨g, hg, eg⟩ := tree_mem [cs0, cs1] hG sp_parts.1 k hk
  have hi := sp_parts.2.1 k hk
  unfold invAt at hi
  obtain ⟨h1, h2⟩ := andB_eq_true hi
  exact ⟨g, hle hg, eg, by rw [eg]; exact Nat.eq_of_beq_eq_true h2, Nat.blt_eq.mp h1⟩

theorem Hyp.normal_cases (H : Hyp z t s f0 f2 q) {R : Subgroup H6}
    (hR : R ≤ Subgroup.centralizer ({s} : Set H6)) (h2 : IsPGroup 2 R)
    (hN : Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6)) :
    R ≤ Subgroup.zpowers s ∨ R = Subgroup.closure (Set.range q) := by
  by_cases hx : ∃ x ∈ R, x ≠ 1 ∧ x ≠ s
  · obtain ⟨x, hxR, hx1, hxs⟩ := hx
    right
    have hRQ := H.le_Q hR h2 hN
    obtain ⟨i, hi, ei⟩ := H.Q_facts.2.2 x (hRQ hxR)
    have hc := (allN_iff _ _).1 sp_parts.2.2.2 i hi
    rcases orB_true hc with h | h
    · exact absurd (eq_of_enc (by rw [ei, enc_one]; exact Nat.eq_of_beq_eq_true h)) hx1
    rcases orB_true h with h | h
    · exact absurd (eq_of_enc (by rw [ei, H.es]; exact Nat.eq_of_beq_eq_true h)) hxs
    obtain ⟨m, hm, hmi⟩ := (anyN_iff _ _).1 h
    have hsq : SQ m = i := Nat.eq_of_beq_eq_true hmi
    have hsp := sp_parts.2.2.1 m hm
    unfold spanAt at hsp
    obtain ⟨-, hsp⟩ := andB_eq_true hsp
    obtain ⟨hk, hsp⟩ := andB_eq_true hsp
    obtain ⟨htr, hso⟩ := andB_eq_true hsp
    have hkl : ∀ l < 5, SKI (Nat.add (Nat.mul 5 m) l) < 12 := fun l hl =>
      Nat.blt_eq.mp ((allN_iff _ _).1 hk l hl)
    choose! kg hkgC hkgK hkgI _ using H.K_mem
    let gens : List H6 := (List.range 5).map fun l =>
      kg (SKI (Nat.add (Nat.mul 5 m) l)) * x * (kg (SKI (Nat.add (Nat.mul 5 m) l)))⁻¹
    have hlen : gens.length = 5 := by simp [gens]
    have hG : ∀ j < gens.length, spanG EQ SQ SKI K KI m j = enc6 (gens.getD j 1) := by
      intro j hj
      rw [hlen] at hj
      have hk' := hkl j hj
      simp only [gens, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
        Option.map_some, Option.getD_some]
      rw [spanG, letN_eq, hsq, ← ei, ← hkgK _ hk', conjF_enc (hkgI _ hk')]
    have ht : ∀ k < 32, treeAt MULF ONE (spanG EQ SQ SKI K KI m) gens.length
        (fun k => SE (Nat.add (Nat.mul 32 m) k)) (fun k => SPP (Nat.add (Nat.mul 32 m) k)) k =
          true := by
      rw [hlen]
      exact fun k hk => (allR_iff _ _ _).1 htr k (Nat.zero_le _) (by omega)
    obtain ⟨-, h32, -⟩ := clos_card_proved enc6_enc gens hG (N := 32) (by norm_num) ht
      (fun k hk => (allR_iff _ _ _).1 hso k (Nat.zero_le _) (by omega))
    have hle : Subgroup.closure {g | g ∈ gens} ≤ R := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [gens, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
      obtain ⟨l, hl, rfl⟩ := hg
      exact (Subgroup.mem_normalizer_iff.mp (hN (hkgC _ (hkl l hl))) x).mp hxR
    have hc32 : 32 ≤ Nat.card R := h32.trans (Subgroup.card_le_of_le hle)
    exact Subgroup.eq_of_le_of_card_ge hRQ (by rw [H.Q_facts.2.1]; exact hc32)
  · left
    intro r hr
    by_cases h1 : r = 1
    · rw [h1]
      exact one_mem _
    · have hrs : r = s := by
        by_contra hne
        exact hx ⟨r, hr, h1, hne⟩
      rw [hrs]
      exact Subgroup.mem_zpowers _

end CertificateChecks.KernelMisc.Sp6Transv.Facts

end
