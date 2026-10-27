module

public import Certificates.Kernel.L34Outer.Checks
public import CFSG.Certificates.Kernel.L34Outer.Group
public import CFSG.Certificates.Kernel.MaxD2.Sound
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34OuterDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL34Outer

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.AGLEmbedding.FusD2 CFSG.AGLEmbedding.L34Outer Certificates.L34Outer

section Abstract

variable {G : Type*} [Group G]

theorem wordVal_mem_of {L : List G} {H : Subgroup G} {k : ℕ} (hL : ∀ j < k, L.getD j 1 ∈ H) :
    ∀ w : List ℤ, (∀ z ∈ w, (0 < z ∧ z ≤ k) ∨ (z < 0 ∧ -(k : ℤ) ≤ z)) → wordVal L w ∈ H
  | [], _ => H.one_mem
  | z :: w, h => by
    rw [wordVal]
    refine H.mul_mem ?_ (wordVal_mem_of hL w fun y hy => h y (List.mem_cons_of_mem z hy))
    rcases h z List.mem_cons_self with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1]
      exact hL _ (by omega)
    · rw [if_neg (by omega)]
      exact H.inv_mem (hL _ (by omega))

theorem wordVal_cons_pos (L : List G) {z : ℤ} (hz : 0 < z) (w : List ℤ) :
    wordVal L (z :: w) = L.getD (z.toNat - 1) 1 * wordVal L w := by
  rw [wordVal, if_pos hz]

theorem mem_normalizer_zpowers' [Finite G] {h y : G} (hy : h * y * h⁻¹ ∈ Subgroup.zpowers y) :
    h ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hy k

theorem ncard_three_le (a b c : G) : Nat.card ({a, b, c} : Set G) ≤ 3 := by
  rw [Nat.card_coe_set_eq]
  refine (Set.ncard_insert_le _ _).trans ?_
  have := Set.ncard_insert_le b {c}
  rw [Set.ncard_singleton] at this
  omega

theorem ncard_four_le (a b c d : G) : Nat.card ({a, b, c, d} : Set G) ≤ 4 := by
  rw [Nat.card_coe_set_eq]
  refine (Set.ncard_insert_le _ _).trans ?_
  have := ncard_three_le b c d
  rw [Nat.card_coe_set_eq] at this
  omega

theorem outer_cover [Finite G] {S T R : Subgroup G} {g1 g2 g3 g4 g5 g6 : G}
    (hS : S = Subgroup.closure {g1, g2, g3}) (hT : T = Subgroup.closure {g1, g2, g3, g4})
    (hR : R = Subgroup.closure {g1, g2, g3, g4, g5, g6})
    (hSn : ∀ c ∈ R, ∀ x ∈ S, c * x * c⁻¹ ∈ S) (hcard : Nat.card R = 12 * Nat.card S)
    (h4 : g4 * (g4 * g4) = 1) (h5 : g5 * g5 = 1) (h6 : g6 * g6 = 1) (h56 : g5 * g6 = g6 * g5)
    (h54 : g5 * (g4 * g5) = g4 * g4) (h64 : g6 * (g4 * g6) = g4 * g4) :
    Nat.card T = 3 * Nat.card S ∧ Nat.card R = 4 * Nat.card T ∧
      (∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T) ∧
      ∀ r ∈ R, ∃ c ∈ ({1, g5, g6, g5 * g6} : Set G), c⁻¹ * r ∈ T := by
  have hgT : ∀ x ∈ ({g1, g2, g3, g4} : Set G), x ∈ T := fun x hx => hT ▸ Subgroup.subset_closure hx
  have hgR : ∀ x ∈ ({g1, g2, g3, g4, g5, g6} : Set G), x ∈ R :=
    fun x hx => hR ▸ Subgroup.subset_closure hx
  have hSgen : ∀ x ∈ ({g1, g2, g3} : Set G), x ∈ S := fun x hx => hS ▸ Subgroup.subset_closure hx
  have hST : S ≤ T := by
    rw [hS, hT]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  have hTR : T ≤ R := by
    rw [hT, hR]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  have i5 : g5⁻¹ = g5 := inv_eq_of_mul_eq_one_right h5
  have i6 : g6⁻¹ = g6 := inv_eq_of_mul_eq_one_right h6
  have i4 : g4⁻¹ = g4 * g4 := inv_eq_of_mul_eq_one_right h4
  have hgen : ∀ a ∈ ({g5, g6} : Set G), a⁻¹ = a ∧ a * (g4 * a) = g4 * g4 := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    exacts [⟨i5, h54⟩, ⟨i6, h64⟩]
  have hconjT : ∀ a ∈ ({g1, g2, g3, g4, g5, g6} : Set G), ∀ t ∈ T, a * t * a⁻¹ ∈ T := by
    intro a ha t ht
    have haR := hgR a ha
    by_cases h56a : a ∈ ({g5, g6} : Set G)
    · obtain ⟨hai, haa⟩ := hgen a h56a
      rw [hT] at ht ⊢
      refine conj_mem_closure (fun s hs => ?_) ht
      by_cases hs4 : s = g4
      · rw [hs4, hai, mul_assoc, haa]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      · have hs3 : s ∈ ({g1, g2, g3} : Set G) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hs4 ⊢
          tauto
        exact hT ▸ hST (hSn a haR _ (hSgen _ hs3))
    · have haT : a ∈ T := hgT a (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha h56a ⊢
        tauto)
      exact T.mul_mem (T.mul_mem haT ht) (T.inv_mem haT)
  have hRN : R ≤ Subgroup.normalizer (T : Set G) := by
    rw [hR, Subgroup.closure_le]
    intro a ha
    exact Subgroup.mem_normalizer_fintype fun t ht => hconjT a ha t ht
  have hN : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T := fun r hr t ht =>
    (Subgroup.mem_normalizer_iff.1 (hRN hr) t).1 ht
  have conjS : ∀ c ∈ R, ∀ x ∈ S, c⁻¹ * x * c ∈ S := fun c hc x hx => by
    have := hSn c⁻¹ (R.inv_mem hc) x hx
    rwa [inv_inv] at this
  have conjT : ∀ c ∈ R, ∀ x ∈ T, c⁻¹ * x * c ∈ T := fun c hc x hx => by
    have := hN c⁻¹ (R.inv_mem hc) x hx
    rwa [inv_inv] at this
  have hCT : ∀ c ∈ ({1, g4, g4 * g4} : Set G), c ∈ T := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc | hc <;> rw [hc]
    · exact T.one_mem
    · exact hgT _ (by simp)
    · exact T.mul_mem (hgT _ (by simp)) (hgT _ (by simp))
  have hcovT := CFSG.KS.L34Outer.cover_of (H := S) (C := ({1, g4, g4 * g4} : Set G))
    (A := {g1, g2, g3, g4}) (by simp) (by
      intro a ha
      by_cases h4a : a = g4
      · refine Or.inr fun c hc => ?_
        rw [h4a, i4]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
        rcases hc with hc | hc | hc <;> rw [hc]
        · simp
        · exact ⟨Or.inr (Or.inr rfl), Or.inl (by rw [mul_assoc, h4])⟩
        · exact ⟨Or.inl h4, Or.inr (Or.inl (by rw [mul_assoc, h4, mul_one]))⟩
      · have haS : a ∈ S := hSgen a (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
          tauto)
        exact Or.inl ⟨haS, fun c hc => conjS c (hTR (hCT c hc)) a haS⟩)
  have hTle : Nat.card T ≤ 3 * Nat.card S := by
    have := CFSG.KS.L34Outer.card_le_of_cover (K := T) (fun x hx => hcovT x (hT ▸ hx))
    exact this.trans (Nat.mul_le_mul_right _ (ncard_three_le _ _ _))
  have hcovR := CFSG.KS.L34Outer.cover_of (H := T) (C := ({1, g5, g6, g5 * g6} : Set G))
    (A := {g1, g2, g3, g4, g5, g6}) (by simp) (by
      intro a ha
      have hCR : ∀ c ∈ ({1, g5, g6, g5 * g6} : Set G), c ∈ R := by
        intro c hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with hc | hc | hc | hc <;> rw [hc]
        · exact R.one_mem
        · exact hgR _ (by simp)
        · exact hgR _ (by simp)
        · exact R.mul_mem (hgR _ (by simp)) (hgR _ (by simp))
      by_cases h5a : a = g5
      · refine Or.inr fun c hc => ?_
        rw [h5a, i5]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
        have e : g5 * (g5 * g6) = g6 := by rw [← mul_assoc, h5, one_mul]
        rcases hc with hc | hc | hc | hc <;> rw [hc]
        · simp
        · simp [h5]
        · simp
        · simp [e]
      by_cases h6a : a = g6
      · refine Or.inr fun c hc => ?_
        rw [h6a, i6]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
        have e : g6 * (g5 * g6) = g5 := by rw [← mul_assoc, ← h56, mul_assoc, h6, mul_one]
        rcases hc with hc | hc | hc | hc <;> rw [hc]
        · simp
        · simp [h56]
        · simp [h6]
        · simp [e]
      have haT : a ∈ T := hgT a (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        tauto)
      exact Or.inl ⟨haT, fun c hc => conjT c (hCR c hc) a haT⟩)
  have hRle : Nat.card R ≤ 4 * Nat.card T := by
    have := CFSG.KS.L34Outer.card_le_of_cover (K := R) (fun x hx => hcovR x (hR ▸ hx))
    exact this.trans (Nat.mul_le_mul_right _ (ncard_four_le _ _ _ _))
  refine ⟨by omega, by omega, hN, fun r hr => hcovR r (hR ▸ hr)⟩

end Abstract

@[expose] def Rp (p : Nat) (x : Equiv.Perm (Fin 42)) : Prop :=
  canonK 42 6 (mask 6) (42 * 6) p = true ∧ TabRep (unpack 42 6 p) x

theorem rp_mul {p q : Nat} {x y : Equiv.Perm (Fin 42)} (hp : Rp p x) (hq : Rp q y) :
    Rp (pcomp 42 6 (mask 6) p q) (x * y) :=
  ⟨cc hp.1 hq.1, by rw [← comp_u hp.1 hq.1]; exact hp.2.comp hq.2⟩

theorem rp_eq {p q : Nat} {x y : Equiv.Perm (Fin 42)} (hp : Rp p x) (hq : Rp q y) :
    p = q ↔ x = y := by
  constructor
  · rintro rfl
    exact hp.2.perm_eq hq.2
  · rintro rfl
    exact u_inj hp.1 hq.1 (hp.2.tab_eq hq.2)

theorem rp_beq {p q : Nat} {x y : Equiv.Perm (Fin 42)} (hp : Rp p x) (hq : Rp q y) :
    Nat.beq p q = true ↔ x = y := by
  rw [← rp_eq hp hq]
  exact ⟨Nat.eq_of_beq_eq_true, fun e => e ▸ Nat.beq_refl p⟩

theorem rp_one : Rp (pidn 42 6) 1 :=
  ⟨pidn_canon ch19768_sz, by rw [← id_u ch19768_sz]; exact TabRep.idTab⟩

theorem rp_inv {p q : Nat} {x : Equiv.Perm (Fin 42)}
    (h : permOK 42 6 (mask 6) (42 * 6) p q = true) (hp : Rp p x) : Rp q x⁻¹ :=
  ⟨(perm_canon h ch19768_sz).2, hp.2.inv (size_u (n := 42) (w := 6) q) (inv_comp h)⟩

theorem rp_unique {p : Nat} {x y : Equiv.Perm (Fin 42)} (hx : Rp p x) (hy : Rp p y) : x = y :=
  hx.2.perm_eq hy.2

theorem rp_word {k : Nat} {L : List (Equiv.Perm (Fin 42))} {PS PSI : Nat → Nat}
    (hk : L.length = k) (hL : ∀ j < k, Rp (PS j) (L.getD j 1))
    (hp : allN k (fun j => permOK 42 6 (mask 6) (42 * 6) (PS j) (PSI j)) = true)
    {wd : List Int} {r : Nat} (h : wordEqK 42 6 (mask 6) (pidn 42 6) PS PSI k wd r = true)
    (hr : canonK 42 6 (mask 6) (42 * 6) r = true) : Rp r (wordVal L wd) := by
  let S : Array Tab := Array.ofFn (n := k) fun j => unpack 42 6 (PS j.val)
  have hS : S.size = k ∧ ∀ j < k, S[j]! = unpack 42 6 (PS j) := by
    refine ⟨by simp [S], fun j hj => ?_⟩
    rw [getElem!_pos S j (by simp [S, hj])]
    simp [S]
  have e := wordT_u hS hp h
  refine ⟨hr, ?_⟩
  rw [← e]
  refine wordT_rep L S (S.map (invTab 42)) (fun j => ?_) (fun j => ?_) wd
  · by_cases hj : j < k
    · have e1 : S.getD j (idTab 42) = unpack 42 6 (PS j) := by simp [S, Array.getD, hj]
      rw [e1]
      exact (hL j hj).2
    · have e1 : S.getD j (idTab 42) = idTab 42 := by simp [S, Array.getD, hj]
      rw [e1, List.getD_eq_default _ _ (by omega)]
      exact TabRep.idTab
  · by_cases hj : j < k
    · have e1 : (S.map (invTab 42)).getD j (idTab 42) = invTab 42 (unpack 42 6 (PS j)) := by
        simp [S, Array.getD, hj]
      rw [e1, inv_u ((PK.allN_iff.1 hp) j hj)]
      exact (rp_inv ((PK.allN_iff.1 hp) j hj) (hL j hj)).2
    · have e1 : (S.map (invTab 42)).getD j (idTab 42) = idTab 42 := by
        simp [S, Array.getD, hj]
      rw [e1, List.getD_eq_default _ _ (by omega), inv_one]
      exact TabRep.idTab

theorem gp_perm {j : Nat} (hj : j < 6) : permOK 42 6 (mask 6) (42 * 6) (GP j) (GPI j) = true :=
  (PK.allN_iff.1 ch19768_gp) j hj

theorem gp_canon {j : Nat} (hj : j < 6) : canonK 42 6 (mask 6) (42 * 6) (GP j) = true :=
  (perm_canon (gp_perm hj) ch19768_sz).1

theorem g1_bind : g₁T = unpack 42 6 (GP 0) := by decide +kernel
theorem g2_bind : g₂T = unpack 42 6 (GP 1) := by decide +kernel
theorem g3_bind : g₃T = unpack 42 6 (GP 2) := by decide +kernel
theorem g4_bind : g₄T = unpack 42 6 (GP 3) := by decide +kernel
theorem g5_bind : g₅T = unpack 42 6 (GP 4) := by decide +kernel
theorem g6_bind : g₆T = unpack 42 6 (GP 5) := by decide +kernel

theorem rp_g1 : Rp (GP 0) g₁ := ⟨gp_canon (by decide), by rw [← g1_bind]; exact tabRep_g₁⟩
theorem rp_g2 : Rp (GP 1) g₂ := ⟨gp_canon (by decide), by rw [← g2_bind]; exact tabRep_g₂⟩
theorem rp_g3 : Rp (GP 2) g₃ := ⟨gp_canon (by decide), by rw [← g3_bind]; exact tabRep_g₃⟩
theorem rp_g4 : Rp (GP 3) g₄ := ⟨gp_canon (by decide), by rw [← g4_bind]; exact tabRep_g₄⟩
theorem rp_g5 : Rp (GP 4) g₅ := ⟨gp_canon (by decide), by rw [← g5_bind]; exact tabRep_g₅⟩
theorem rp_g6 : Rp (GP 5) g₆ := ⟨gp_canon (by decide), by rw [← g6_bind]; exact tabRep_g₆⟩

theorem hL6 : ∀ j < 6, Rp (GP j) (g6.getD j 1) := by
  intro j hj
  interval_cases j <;> simp only [g6, List.getD_cons_zero, List.getD_cons_succ]
  exacts [rp_g1, rp_g2, rp_g3, rp_g4, rp_g5, rp_g6]

theorem hL4 : ∀ j < 4, Rp (GP j) (g4.getD j 1) := by
  intro j hj
  interval_cases j <;> simp only [g4, List.getD_cons_zero, List.getD_cons_succ]
  exacts [rp_g1, rp_g2, rp_g3, rp_g4]

theorem hL3 : ∀ j < 3, Rp (GP j) ([g₁, g₂, g₃].getD j 1) := by
  intro j hj
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ]
  exacts [rp_g1, rp_g2, rp_g3]

theorem gp_allN (k : Nat) (hk : k ≤ 6) :
    allN k (fun j => permOK 42 6 (mask 6) (42 * 6) (GP j) (GPI j)) = true :=
  PK.allN_iff.2 fun j hj => gp_perm (by omega)

theorem rp_w4 {wd : List Int} {r : Nat}
    (h : wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 4 wd r = true)
    (hr : canonK 42 6 (mask 6) (42 * 6) r = true) : Rp r (wordVal g4 wd) :=
  rp_word (k := 4) (L := g4) rfl hL4 (gp_allN 4 (by decide)) h hr

theorem rp_w6 {wd : List Int} {r : Nat}
    (h : wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 6 wd r = true)
    (hr : canonK 42 6 (mask 6) (42 * 6) r = true) : Rp r (wordVal g6 wd) :=
  rp_word (k := 6) (L := g6) rfl hL6 (gp_allN 6 (by decide)) h hr

theorem rp_w3 {wd : List Int} {r : Nat}
    (h : wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 3 wd r = true)
    (hr : canonK 42 6 (mask 6) (42 * 6) r = true) : Rp r (wordVal [g₁, g₂, g₃] wd) :=
  rp_word (k := 3) (L := [g₁, g₂, g₃]) rfl hL3 (gp_allN 3 (by decide)) h hr

theorem rels : g₄ * (g₄ * g₄) = 1 ∧ g₅ * g₅ = 1 ∧ g₆ * g₆ = 1 ∧ g₅ * g₆ = g₆ * g₅ ∧
    g₅ * (g₄ * g₅) = g₄ * g₄ ∧ g₆ * (g₄ * g₆) = g₄ * g₄ :=
  ⟨(rp_beq (rp_mul rp_g4 (rp_mul rp_g4 rp_g4)) rp_one).1 ch19768_r4,
    (rp_beq (rp_mul rp_g5 rp_g5) rp_one).1 ch19768_r5,
    (rp_beq (rp_mul rp_g6 rp_g6) rp_one).1 ch19768_r6,
    (rp_beq (rp_mul rp_g5 rp_g6) (rp_mul rp_g6 rp_g5)).1 ch19768_r56,
    (rp_beq (rp_mul rp_g5 (rp_mul rp_g4 rp_g5)) (rp_mul rp_g4 rp_g4)).1 ch19768_r54,
    (rp_beq (rp_mul rp_g6 (rp_mul rp_g4 rp_g6)) (rp_mul rp_g4 rp_g4)).1 ch19768_r64⟩

theorem outer_TR :
    Nat.card L34T = 3 * Nat.card S ∧ Nat.card R = 4 * Nat.card L34T ∧
      (∀ r ∈ R, ∀ t ∈ L34T, r * t * r⁻¹ ∈ L34T) ∧
      ∀ r ∈ R, ∃ c ∈ ({1, g₅, g₆, g₅ * g₆} : Set (Equiv.Perm (Fin 42))), c⁻¹ * r ∈ L34T := by
  obtain ⟨h4, h5, h6, h56, h54, h64⟩ := rels
  exact outer_cover (S := S) (T := L34T) (R := R) rfl rfl rfl (fun c hc x hx => conj_mem_S hc hx)
    (by rw [card_S, card_R]) h4 h5 h6 h56 h54 h64

theorem cardT : Nat.card L34T = 60480 := by
  rw [outer_TR.1, card_S]

theorem order3 : ∀ r ∈ R, r ^ 3 = 1 → r ∈ L34T := by
  intro r hr h3
  refine CFSG.KS.L34Outer.mem_of_pow_three T_le_R outer_TR.2.2.1 outer_TR.2.1 hr h3

theorem pair_set {α β : Type*} (f : α → β) (p q : α) :
    {g | g ∈ [p, q].map f} = ({f p, f q} : Set β) := by
  ext g
  simp [eq_comm]

theorem enum_facts {k cnt cap : Nat} {G GI T PL POS SRT SRI : Nat → Nat} (hk : k = 2)
    (hh : penumHdK (pidn 42 6) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false G GI k cnt T PL POS SRT SRI i = true)
    {x y : Equiv.Perm (Fin 42)} (hx : Rp (G 0) x) (hy : Rp (G 1) y) :
    Nat.card (Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 42)))) = cnt ∧
      (∀ i < cnt, ∃ g ∈ Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 42))), Rp (T i) g) ∧
      ∀ g ∈ Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 42))), ∃ i < cnt, Rp (T i) g := by
  subst hk
  let gs : Array Tab := #[unpack 42 6 (G 0), unpack 42 6 (G 1)]
  have hg : GensOK 42 6 2 G gs := by
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j
    · exact ⟨rfl, hx.1⟩
    · exact ⟨rfl, hy.1⟩
  have hok := (penumK_left_sound ch19768_sz hg hh hp).2
  have hE : Enumerates (Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 42))))
      (penumRec 42 6 cnt T PL).tabs.toList := by
    refine enumerates_closure (gens := gs) (fun a ha => ?_) (fun j hj => ?_) hok
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨0, by simp [gs], hx.2⟩
      · exact ⟨1, by simp [gs], hy.2⟩
    · have hj' : j < 2 := hj
      interval_cases j
      · exact ⟨x, by simp, hx.2⟩
      · exact ⟨y, by simp, hy.2⟩
  refine ⟨by rw [hE.card, Array.length_toList, rec_size], fun i hi => ?_, fun g hg' => ?_⟩
  · obtain ⟨g, hg1, hg2⟩ := hE.exists_elt (by rw [rec_size]; exact hi)
    rw [rec_get hi] at hg2
    exact ⟨g, hg1, penumPt_canon (hp i hi), hg2⟩
  · obtain ⟨i, hi, hr⟩ := hE.exists_pos hg'
    rw [rec_size] at hi
    rw [rec_get hi] at hr
    exact ⟨i, hi, penumPt_canon (hp i hi), hr⟩

theorem pgc (j : Nat) (hj : j < 2) : canonK 42 6 (mask 6) (42 * 6) (PE.G j) = true :=
  (PK.allN_iff.1 ch19768_pgc) j hj

theorem rp_a : Rp (PE.G 0) (wordVal g4 l34OuterData.a) := rp_w4 ch19768_pa (pgc 0 (by decide))

theorem rp_b : Rp (PE.G 1) (wordVal g4 l34OuterData.b) := rp_w4 ch19768_pb (pgc 1 (by decide))

theorem psub_eq : Psub l34OuterData = Subgroup.closure
    ({wordVal g4 l34OuterData.a, wordVal g4 l34OuterData.b} : Set (Equiv.Perm (Fin 42))) := by
  unfold Psub
  rw [pair_set]

theorem P_facts : Nat.card (Psub l34OuterData) = 27 ∧
    (∀ i < 27, ∃ g ∈ Psub l34OuterData, Rp (PE.T i) g) ∧
    ∀ g ∈ Psub l34OuterData, ∃ i < 27, Rp (PE.T i) g := by
  rw [psub_eq]
  exact enum_facts (cnt := PE.cnt) rfl ch19768_ph
    (fun i hi => penumSl_spec ch19768_ps i (Nat.zero_le _) (by exact hi) hi) rp_a rp_b

theorem egc {e j : Nat} (he : e < 4) (hj : j < 2) : canonK 42 6 (mask 6) (42 * 6) (EG e j) = true :=
  (PK.allN_iff.1 ((PK.allN_iff.1 ch19768_egc) e he)) j hj

theorem rp_u {e : Nat} (he : e < 4) : Rp (EG e 0) (wordVal g4 (l34OuterData.es[e]!).u) :=
  rp_w4 ((PK.allN_iff.1 ch19768_eu) e he) (egc he (by decide))

theorem rp_v {e : Nat} (he : e < 4) : Rp (EG e 1) (wordVal g4 (l34OuterData.es[e]!).v) :=
  rp_w4 ((PK.allN_iff.1 ch19768_ev) e he) (egc he (by decide))

theorem esub_eq (e : EData) : Esub e = Subgroup.closure
    ({wordVal g4 e.u, wordVal g4 e.v} : Set (Equiv.Perm (Fin 42))) := by
  unfold Esub
  rw [pair_set]

theorem E_facts {e : Nat} (he : e < 4) : Nat.card (Esub l34OuterData.es[e]!) = 9 ∧
    (∀ i < 9, ∃ g ∈ Esub l34OuterData.es[e]!, Rp (ET e i) g) ∧
    ∀ g ∈ Esub l34OuterData.es[e]!, ∃ i < 9, Rp (ET e i) g := by
  rw [esub_eq]
  have hu := rp_u he
  have hv := rp_v he
  interval_cases e
  · exact enum_facts (cnt := E0.cnt) rfl ch19768_e0h
      (fun i hi => penumSl_spec ch19768_e0s i (Nat.zero_le _) (by exact hi) hi) hu hv
  · exact enum_facts (cnt := E1.cnt) rfl ch19768_e1h
      (fun i hi => penumSl_spec ch19768_e1s i (Nat.zero_le _) (by exact hi) hi) hu hv
  · exact enum_facts (cnt := E2.cnt) rfl ch19768_e2h
      (fun i hi => penumSl_spec ch19768_e2s i (Nat.zero_le _) (by exact hi) hi) hu hv
  · exact enum_facts (cnt := E3.cnt) rfl ch19768_e3h
      (fun i hi => penumSl_spec ch19768_e3s i (Nat.zero_le _) (by exact hi) hi) hu hv

theorem es_length : l34OuterData.es.length = 4 := rfl

theorem mem_es {e : EData} (he : e ∈ l34OuterData.es) : ∃ i < 4, e = l34OuterData.es[i]! := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
  exact ⟨i, es_length ▸ hi, (getElem!_pos _ i hi).symm⟩

theorem es_mem {i : Nat} (hi : i < 4) : l34OuterData.es[i]! ∈ l34OuterData.es := by
  rw [getElem!_pos _ i (es_length ▸ hi)]
  exact List.getElem_mem _

theorem rp_z : Rp (E0.G 0) (zel l34OuterData) := by
  have h := rp_u (e := 0) (by decide)
  have e1 : (l34OuterData.es[0]!).u = l34OuterData.z := rfl
  rw [e1] at h
  exact h

theorem z_ne : zel l34OuterData ≠ 1 := fun h1 => by
  have h := ch19768_zne
  rw [(rp_beq rp_z rp_one).2 h1] at h
  exact absurd h (by decide)

theorem z_mem : ∀ e ∈ l34OuterData.es, zel l34OuterData ∈ Esub e := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := mem_es he
  unfold Esub zel
  refine Subgroup.subset_closure (List.mem_map.2 ⟨l34OuterData.z, ?_, rfl⟩)
  interval_cases i <;> decide

theorem noncomm : wordVal g4 l34OuterData.a * wordVal g4 l34OuterData.b ≠
    wordVal g4 l34OuterData.b * wordVal g4 l34OuterData.a := fun h1 => by
  have h := ch19768_nc
  rw [(rp_beq (rp_mul rp_a rp_b) (rp_mul rp_b rp_a)).2 h1] at h
  exact absurd h (by decide)

theorem pt_mem {i : Nat} (hi : i < 27) {g : Equiv.Perm (Fin 42)} (hg : Rp (PE.T i) g) :
    g ∈ Psub l34OuterData := by
  obtain ⟨g', hg', hr⟩ := P_facts.2.1 i hi
  rwa [rp_unique hg hr]

theorem E_le_P {e : Nat} (he : e < 4) : Esub l34OuterData.es[e]! ≤ Psub l34OuterData := by
  rw [esub_eq, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have hs := (PK.allN_iff.1 ((PK.allN_iff.1 ch19768_sub) e he))
  rcases hg with rfl | rfl
  · obtain ⟨h1, h2⟩ := band_e (hs 0 (by decide))
    refine pt_mem (Nat.blt_eq.mp h1) ?_
    rw [Nat.eq_of_beq_eq_true h2]
    exact rp_u he
  · obtain ⟨h1, h2⟩ := band_e (hs 1 (by decide))
    refine pt_mem (Nat.blt_eq.mp h1) ?_
    rw [Nat.eq_of_beq_eq_true h2]
    exact rp_v he

theorem cover : ∀ g ∈ Psub l34OuterData, ∃ E ∈ l34OuterData.es.map Esub, g ∈ E := by
  intro g hg
  obtain ⟨i, hi, hr⟩ := P_facts.2.2 g hg
  have h := (PK.allN_iff.1 ch19768_cv) i hi
  rw [PK.strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_e h
  obtain ⟨h2, h3⟩ := band_e h2
  have he := Nat.blt_eq.mp h1
  obtain ⟨g', hg', hr'⟩ := (E_facts he).2.1 _ (Nat.blt_eq.mp h2)
  rw [Nat.eq_of_beq_eq_true h3] at hr'
  exact ⟨_, List.mem_map.2 ⟨_, es_mem he, rfl⟩, by rwa [rp_unique hr hr']⟩

theorem center : ∀ g ∈ Psub l34OuterData, (∀ p ∈ Psub l34OuterData, g * p = p * g) →
    g = 1 ∨ g = zel l34OuterData ∨ g = zel l34OuterData * zel l34OuterData := by
  intro g hg hc
  obtain ⟨i, hi, hr⟩ := P_facts.2.2 g hg
  have h := (PK.allN_iff.1 ch19768_ctr) i hi
  rw [PK.strictB_eq] at h
  by_cases c1 : Nat.beq (PE.T i) (pidn 42 6) = true
  · exact Or.inl ((rp_beq hr rp_one).1 c1)
  have h := bif_f (Bool.eq_false_iff.2 c1) h
  by_cases c2 : Nat.beq (PE.T i) (E0.G 0) = true
  · exact Or.inr (Or.inl ((rp_beq hr rp_z).1 c2))
  have h := bif_f (Bool.eq_false_iff.2 c2) h
  by_cases c3 : Nat.beq (PE.T i) (pcomp 42 6 (mask 6) (E0.G 0) (E0.G 0)) = true
  · exact Or.inr (Or.inr ((rp_beq hr (rp_mul rp_z rp_z)).1 c3))
  have h := bif_f (Bool.eq_false_iff.2 c3) h
  have hca := hc (wordVal g4 l34OuterData.a) (by
    rw [psub_eq]
    exact Subgroup.subset_closure (by simp))
  have hcb := hc (wordVal g4 l34OuterData.b) (by
    rw [psub_eq]
    exact Subgroup.subset_closure (by simp))
  have h := bif_t ((rp_beq (rp_mul hr rp_a) (rp_mul rp_a hr)).2 hca) h
  have h := bif_t ((rp_beq (rp_mul hr rp_b) (rp_mul rp_b hr)).2 hcb) h
  exact absurd h (by decide)

theorem pairs : ∀ x ∈ Psub l34OuterData, ∀ y ∈ Psub l34OuterData,
    Nat.card (Subgroup.closure {x, y}) = 9 →
      ∃ e ∈ l34OuterData.es, Subgroup.closure {x, y} = Esub e := by
  intro x hx y hy hcard
  have hHP : Subgroup.closure {x, y} ≤ Psub l34OuterData := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    exacts [hx, hy]
  obtain ⟨E, hE, hHE⟩ := CFSG.KS.L34Outer.eq_of_card_nine P_facts.1 (fun E hE => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hE
      obtain ⟨i, hi, rfl⟩ := mem_es he
      exact ⟨E_le_P hi, (E_facts hi).1⟩) cover center hHP hcard
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hE
  exact ⟨e, he, hHE⟩

theorem inS : ∀ e ∈ l34OuterData.es, e.inS = true → Esub e ≤ S := by
  intro e he hS
  obtain ⟨i, hi, rfl⟩ := mem_es he
  interval_cases i
  rotate_left
  · exact absurd hS (by decide)
  · exact absurd hS (by decide)
  · exact absurd hS (by decide)
  rw [esub_eq, Subgroup.closure_le]
  have hmem : ∀ w, wordVal [g₁, g₂, g₃] w ∈ S := wordVal_mem _ S (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    exacts [g₁_mem_S, g₂_mem_S, g₃_mem_S])
  have hw := PK.allN_iff.1 ch19768_sw
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [rp_unique (rp_u (e := 0) (by decide)) (rp_w3 (hw 0 (by decide)) (egc (e := 0) (by decide)
      (by decide)))]
    exact hmem _
  · rw [rp_unique (rp_v (e := 0) (by decide)) (rp_w3 (hw 1 (by decide)) (egc (e := 0) (by decide)
      (by decide)))]
    exact hmem _

theorem hp_perm {e j : Nat} (he : e < 3) (hj : j < 2) :
    permOK 42 6 (mask 6) (42 * 6) (HP (Nat.add (Nat.mul 2 e) j)) (HPI (Nat.add (Nat.mul 2 e) j)) =
      true :=
  (band_e ((PK.allN_iff.1 ((PK.allN_iff.1 ch19768_hw) e he)) j hj)).2

theorem rp_h {e j : Nat} (he : e < 3) (hj : j < 2) :
    Rp (HP (Nat.add (Nat.mul 2 e) j)) (wordVal g4 ((l34OuterData.es[Nat.succ e]!).hs[j]!)) :=
  rp_w4 (band_e ((PK.allN_iff.1 ((PK.allN_iff.1 ch19768_hw) e he)) j hj)).1
    (perm_canon (hp_perm he hj) ch19768_sz).1

theorem exhibit_h {e j : Nat} (he : e < 3) (hj : j < 2) :
    ∃ y ∈ Esub l34OuterData.es[Nat.succ e]!, y ≠ 1 ∧
      wordVal g4 ((l34OuterData.es[Nat.succ e]!).hs[j]!) ∈
        Subgroup.normalizer (Subgroup.zpowers y : Set (Equiv.Perm (Fin 42))) := by
  have h := (PK.allN_iff.1 ((PK.allN_iff.1 ch19768_y) e he)) j hj
  unfold yK at h
  rw [PK.strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_e h
  obtain ⟨-, h3⟩ := band_e h2
  obtain ⟨h3, h4⟩ := band_e h3
  obtain ⟨y, hy, hr⟩ := (E_facts (e := Nat.succ e) (by omega)).2.1 _ (Nat.blt_eq.mp h1)
  refine ⟨y, hy, fun h1' => ?_, ?_⟩
  · rw [(rp_beq hr rp_one).2 h1'] at h3
    exact absurd h3 (by decide)
  · apply mem_normalizer_zpowers'
    have hc := (rp_beq (rp_mul (rp_h he hj) hr) (rp_mul hr (rp_h he hj))).1 h4
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers y

theorem exhibit : ∀ e ∈ l34OuterData.es, e.inS = false → ∃ L : List (Equiv.Perm (Fin 42)),
    (∀ h ∈ L, h ∈ L34T ∧ ∃ y ∈ Esub e, y ≠ 1 ∧
      h ∈ Subgroup.normalizer (Subgroup.zpowers y : Set (Equiv.Perm (Fin 42)))) ∧
    Subgroup.closure {h | h ∈ L} = L34T := by
  intro e he hS
  obtain ⟨i, hi, rfl⟩ := mem_es he
  obtain ⟨k, hk, rfl⟩ : ∃ k < 3, i = Nat.succ k := by
    rcases i with _ | k
    · exact absurd hS (by decide)
    · exact ⟨k, by omega, rfl⟩
  let hw := fun j : Nat => wordVal g4 ((l34OuterData.es[Nat.succ k]!).hs[j]!)
  refine ⟨[hw 0, hw 1], fun h hh => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact ⟨wordVal_g4_mem _, exhibit_h hk (by decide)⟩
    · exact ⟨wordVal_g4_mem _, exhibit_h hk (by decide)⟩
  · refine le_antisymm ((Subgroup.closure_le _).2 fun h hh => ?_) ?_
    · simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl <;> exact wordVal_g4_mem _
    · have hL2 : ∀ l < 2, Rp (HP (Nat.add (Nat.mul 2 k) l)) ([hw 0, hw 1].getD l 1) := by
        intro l hl
        interval_cases l
        · exact rp_h hk (by decide)
        · exact rp_h hk (by decide)
      have hp2 : allN 2 (fun l => permOK 42 6 (mask 6) (42 * 6) (HP (Nat.add (Nat.mul 2 k) l))
          (HPI (Nat.add (Nat.mul 2 k) l))) = true :=
        PK.allN_iff.2 fun l hl => hp_perm hk hl
      have hgen : ∀ m < 4, g4.getD m 1 ∈ Subgroup.closure {h | h ∈ [hw 0, hw 1]} := by
        intro m hm
        have h := (PK.allN_iff.1 ((PK.allN_iff.1 ch19768_gen) k hk)) m hm
        unfold genK at h
        have hr := rp_word (k := 2) (L := [hw 0, hw 1]) rfl hL2 hp2 h (gp_canon (by omega))
        rw [← rp_unique hr (hL4 m hm)]
        exact wordVal_mem _ _ (fun g hg => Subgroup.subset_closure hg) _
      rw [L34T, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hgen 0 (by decide)
      · exact hgen 1 (by decide)
      · exact hgen 2 (by decide)
      · exact hgen 3 (by decide)

theorem rp_x {j : Nat} (hj : j < 3) : Rp (XP j) (wordVal g6 (xW[j]!)) := by
  have h := (PK.allN_iff.1 ch19768_x) j hj
  unfold xK at h
  obtain ⟨h1, h2⟩ := band_e h
  exact rp_w6 h1 (band_e h2).1

theorem x_norm {j : Nat} (hj : j < 3) : wordVal g6 (xW[j]!) ∈
    Subgroup.normalizer (Subgroup.zpowers (zel l34OuterData) : Set (Equiv.Perm (Fin 42))) := by
  have h := (PK.allN_iff.1 ch19768_x) j hj
  unfold xK at h
  have h3 := (band_e (band_e h).2).2
  have hc := (rp_beq (rp_mul (rp_x hj) rp_z) (rp_mul (rp_mul rp_z rp_z) (rp_x hj))).1 h3
  apply mem_normalizer_zpowers'
  rw [hc, mul_inv_cancel_right]
  exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem g6_mem_T : ∀ j < 4, g6.getD j 1 ∈ L34T := by
  intro j hj
  interval_cases j <;> simp only [g6, List.getD_cons_zero, List.getD_cons_succ] <;>
    exact Subgroup.subset_closure (by simp)

theorem x_coset {c t r : Equiv.Perm (Fin 42)} (ht : t ∈ L34T) (hr : c⁻¹ * r ∈ L34T) :
    (c * t)⁻¹ * r ∈ L34T := by
  rw [mul_inv_rev, mul_assoc]
  exact L34T.mul_mem (L34T.inv_mem ht) hr

theorem extras : ∃ X : List (Equiv.Perm (Fin 42)),
    (∀ x ∈ X, x ∈ R ∧
      x ∈ Subgroup.normalizer (Subgroup.zpowers (zel l34OuterData) : Set (Equiv.Perm (Fin 42)))) ∧
    ∀ r ∈ R, r ∈ L34T ∨ ∃ x ∈ X, x⁻¹ * r ∈ L34T := by
  refine ⟨[wordVal g6 (xW[0]!), wordVal g6 (xW[1]!), wordVal g6 (xW[2]!)], fun x hx => ?_,
    fun r hr => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨wordVal_g6_mem _, x_norm (by decide)⟩
    · exact ⟨wordVal_g6_mem _, x_norm (by decide)⟩
    · exact ⟨wordVal_g6_mem _, x_norm (by decide)⟩
  obtain ⟨c, hc, hcr⟩ := outer_TR.2.2.2 r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  have hT : ∀ w : List ℤ, (∀ z ∈ w, (0 < z ∧ z ≤ (4 : ℕ)) ∨ (z < 0 ∧ -((4 : ℕ) : ℤ) ≤ z)) →
      wordVal g6 w ∈ L34T := wordVal_mem_of g6_mem_T
  rcases hc with rfl | rfl | rfl | rfl
  · left
    simpa using hcr
  · right
    refine ⟨_, List.mem_cons_self, ?_⟩
    have ex : xW[0]! = 5 :: [1, 2, -1] := rfl
    have e : wordVal g6 (xW[0]!) = g₅ * wordVal g6 [1, 2, -1] := by
      rw [ex, wordVal_cons_pos _ (by decide)]
      rfl
    rw [e]
    exact x_coset (hT _ (by decide)) hcr
  · right
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    have ex : xW[1]! = 6 :: [2, -1, 3, 1, 2, -4, 1, 2] := rfl
    have e : wordVal g6 (xW[1]!) = g₆ * wordVal g6 [2, -1, 3, 1, 2, -4, 1, 2] := by
      rw [ex, wordVal_cons_pos _ (by decide)]
      rfl
    rw [e]
    exact x_coset (hT _ (by decide)) hcr
  · right
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
    have e : wordVal g6 (xW[2]!) = g₅ * g₆ * wordVal g6 [-1, 3, 1, 2, -4, 1, 2] := by
      have ex : xW[2]! = 5 :: 6 :: [-1, 3, 1, 2, -4, 1, 2] := rfl
      rw [ex, wordVal_cons_pos _ (by decide),
        wordVal_cons_pos _ (by decide), mul_assoc]
      rfl
    rw [e]
    exact x_coset (hT _ (by decide)) hcr

theorem outerFacts_l34 : OuterFacts l34OuterData :=
  ⟨cardT, order3, P_facts.1, Psub_le_T _, noncomm, pairs, inS, z_ne, z_mem, exhibit, extras⟩

end CertificateChecks.KernelL34Outer

end
