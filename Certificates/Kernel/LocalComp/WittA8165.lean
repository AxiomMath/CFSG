module

public import Certificates.Kernel.LocalComp.WittA2034
public import Certificates.Kernel.LocalComp.WittK8165
public import CFSG.Certificates.Kernel.WittFixSound
public import CFSG.RankThree.PartTwo.KFacts.KP4Data

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign
  CertificateChecks.KernelSpor.M22Syl CFSG.RankThree.PartTwo.KFacts.KP4

theorem pkw_wordPerm (w : List Bool) : pkw 5 (wordPerm w) = pwp A B I w :=
  pwp_pkw pk_a pk_b pk_one w

theorem count_tr (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q]
    (b : Nat → Bool) (hb : ∀ τ : Perm (Fin 22), b (pkw 5 τ) = decide (Q ⇑τ)) (w : List Bool)
    (e₀ e₁ e₂ : Fin 22) (h₀ : pt (pwp A B I w) e₀.val = 0) (h₁ : pt (pwp A B I w) e₁.val = 1)
    (h₂ : pt (pwp A B I w) e₂.val = 2) (C0 : Nat → Bool) (C1 : Nat → Nat → Bool)
    (C2 : Nat → Nat → Nat → Bool)
    (hQ : ∀ f : Perm (Fin 22), Q ⇑f →
      C0 (f e₀).val = true ∧ C1 (f e₀).val (f e₁).val = true ∧
        C2 (f e₀).val (f e₁).val (f e₂).val = true) :
    m22Count Q = wcB b (pwp A B I w) C0 C1 C2 := by
  refine m22Count_eq_wcB Q b hb (wordPerm w) (wordPerm_mem w) _ (pkw_wordPerm w) C0 C1 C2
    fun σ h => ?_
  have := hQ _ h
  rwa [mul_apply_of_pk (pkw_wordPerm w) σ (i := 0) h₀,
    mul_apply_of_pk (pkw_wordPerm w) σ (i := 1) h₁,
    mul_apply_of_pk (pkw_wordPerm w) σ (i := 2) h₂] at this

theorem fix_of_comm {f t : Fin 22 → Fin 22} (h : ∀ p, f (t p) = t (f p)) {e : Fin 22}
    (he : t e = e) : t (f e) = f e := by
  rw [← h, he]

theorem count_line (i : Fin 4) (T X : Nat)
    (hT : ∀ x : Fin 22, pt T x.val = (ofTab (lineTab i) x).val)
    (hX : ∀ x : Fin 22, ofTab (lineTab i) x = x → inM X x.val = true) (w : List Bool)
    (e₀ e₁ e₂ : Fin 22) (f₀ : ofTab (lineTab i) e₀ = e₀) (f₁ : ofTab (lineTab i) e₁ = e₁)
    (f₂ : ofTab (lineTab i) e₂ = e₂) (h₀ : pt (pwp A B I w) e₀.val = 0)
    (h₁ : pt (pwp A B I w) e₁.val = 1) (h₂ : pt (pwp A B I w) e₂.val = 2) :
    m22Count (fun f => ∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) =
        wcB (relT T T) (pwp A B I w) (inM X) (fun _ => inM X) (fun _ _ => inM X) ∧
      m22Count (fun f => (∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) ∧
          ∀ p, f (f (f (f p))) = p) =
        wcB (fun y => relT T T y && fourB y) (pwp A B I w) (inM X) (fun _ => inM X)
          (fun _ _ => inM X) := by
  have hr : ∀ τ : Perm (Fin 22), relT T T (pkw 5 τ) =
      decide (∀ p, τ (ofTab (lineTab i) p) = ofTab (lineTab i) (τ p)) := fun τ =>
    relT_pkw τ _ _ T T hT hT
  have hc : ∀ f : Fin 22 → Fin 22, (∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) →
      inM X (f e₀).val = true ∧ inM X (f e₁).val = true ∧ inM X (f e₂).val = true :=
    fun f h => ⟨hX _ (fix_of_comm h f₀), hX _ (fix_of_comm h f₁), hX _ (fix_of_comm h f₂)⟩
  have h4 : ∀ τ : Perm (Fin 22), (relT T T (pkw 5 τ) && fourB (pkw 5 τ)) =
      decide ((∀ p, τ (ofTab (lineTab i) p) = ofTab (lineTab i) (τ p)) ∧
        ∀ p, τ (τ (τ (τ p))) = p) := fun τ => by
    rw [hr, fourB_pkw, Bool.decide_and]
  exact ⟨count_tr (fun f => ∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) (relT T T) hr
      w e₀ e₁ e₂ h₀ h₁ h₂ (inM X) (fun _ => inM X) (fun _ _ => inM X) fun f h => hc f h,
    count_tr (fun f => (∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) ∧
      ∀ p, f (f (f (f p))) = p) (fun y => relT T T y && fourB y) h4 w e₀ e₁ e₂ h₀ h₁ h₂ (inM X)
      (fun _ => inM X) (fun _ _ => inM X) fun f h => hc f h.1⟩

theorem trW_lt : ∀ p ∈ trW, ∀ i ∈ p.1, i < 22 := by decide +kernel

theorem trW_len : ∀ p ∈ trW, p.1 = [p.1.getD 0 0, p.1.getD 1 0, p.1.getD 2 0] := by
  decide +kernel

@[expose] def blk (x : Fin 22) : Fin 3 := if x.val < 8 then 0 else if x.val < 15 then 1 else 2

theorem cover_dec : ∀ a b c : Fin 22, a ≠ b → a ≠ c → b ≠ c → blk a = blk b → blk a = blk c →
    ∃ p ∈ trW, ∀ i ∈ p.1, i = a.val ∨ i = b.val ∨ i = c.val := by
  decide +kernel

theorem cover (S : Finset (Fin 22)) (hS : 7 ≤ S.card) :
    ∃ p ∈ trW, ∀ i ∈ p.1, ∀ h : i < 22, (⟨i, h⟩ : Fin 22) ∈ S := by
  have h3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have key : ∃ k : Fin 3, 3 ≤ (S.filter fun x => blk x = k).card := by
    by_contra hne
    push Not at hne
    have hsub : S ⊆ (S.filter fun x => blk x = 0) ∪ (S.filter fun x => blk x = 1) ∪
        (S.filter fun x => blk x = 2) := by
      intro x hx
      rcases h3 (blk x) with h | h | h <;> simp [hx, h]
    have hc := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have h0 := hne 0
    have h1 := hne 1
    have h2 := hne 2
    omega
  obtain ⟨k, hk⟩ := key
  obtain ⟨u, hu, hu3⟩ := Finset.exists_subset_card_eq hk
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hu3
  have hx := Finset.mem_filter.1 (hu (by simp : x ∈ ({x, y, z} : Finset (Fin 22))))
  have hy := Finset.mem_filter.1 (hu (by simp : y ∈ ({x, y, z} : Finset (Fin 22))))
  have hz := Finset.mem_filter.1 (hu (by simp : z ∈ ({x, y, z} : Finset (Fin 22))))
  obtain ⟨p, hp, hpe⟩ := cover_dec x y z hxy hxz hyz (hx.2.trans hy.2.symm)
    (hx.2.trans hz.2.symm)
  refine ⟨p, hp, fun i hi h => ?_⟩
  rcases hpe i hi with rfl | rfl | rfl
  · exact hx.1
  · exact hy.1
  · exact hz.1

abbrev Q7 (e : List Nat) (f : Fin 22 → Fin 22) : Prop :=
  (∀ i ∈ e, ∀ h : i < 22, f ⟨i, h⟩ = ⟨i, h⟩) ∧ 7 ≤ (Finset.univ.filter fun p => f p = p).card ∧
    ¬ ∀ x, f x = x

theorem fix7T_pkw {e : List Nat} (he : ∀ i ∈ e, i < 22) (τ : Perm (Fin 22)) :
    fix7T e (pkw 5 τ) = decide (Q7 e ⇑τ) := by
  have g : ∀ a b c : Bool, Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) true false c)
        b) a = (a && (b && !c)) := by decide
  have e1 : fix7T e (pkw 5 τ) =
      (fixL e (pkw 5 τ) && (Nat.ble (nat_lit 7) (fixC (pkw 5 τ)) && !Nat.beq (pkw 5 τ) I)) :=
    g _ _ _
  have e2 : Nat.beq (pkw 5 τ) I = true ↔ ∀ x, τ x = x := by
    rw [← KernelSpor.M22Syl.pk_one, beq_pkw_iff (by norm_num), Equiv.Perm.ext_iff]
    rfl
  rw [e1, Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', fixL_pkw τ he,
    Nat.ble_eq, fixC_pkw, decide_eq_true_iff, Bool.eq_false_iff, ne_eq, e2]

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem trAll_sound : ∀ L : List (List Nat × List Bool), trAll L = true →
    ∀ p ∈ L, trOK p.1 p.2 = true
  | [], _ => by simp
  | q :: L, h => by
    have h' : trAll (q :: L) = (trOK q.1 q.2 && trAll L) := bAnd_eq _ _
    rw [h', Bool.and_eq_true] at h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact trAll_sound L h.2 p hp

theorem no_Q7 {p : List Nat × List Bool} (hp : p ∈ trW) :
    ∀ g : M22, ¬ Q7 p.1 ⇑(g : Perm (Fin 22)) := by
  intro g hg
  have hok := trAll_sound trW k8165c p hp
  have hlt := trW_lt p hp
  have hl := trW_len p hp
  set e := p.1 with he_def
  have l0 : e.getD 0 0 < 22 := hlt _ (by rw [hl]; simp)
  have l1 : e.getD 1 0 < 22 := hlt _ (by rw [hl]; simp)
  have l2 : e.getD 2 0 < 22 := hlt _ (by rw [hl]; simp)
  unfold trOK at hok
  rw [strictB_eq', bAnd_eq, bAnd_eq, bAnd_eq] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨h0, h1, h2, hz⟩ := hok
  have hc := count_tr (Q7 e) (fix7T e) (fix7T_pkw hlt) p.2 ⟨_, l0⟩ ⟨_, l1⟩ ⟨_, l2⟩
    (Nat.eq_of_beq_eq_true h0) (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
    (fun x => Nat.beq x (e.getD 0 0)) (fun _ x => Nat.beq x (e.getD 1 0))
    (fun _ _ x => Nat.beq x (e.getD 2 0)) fun f hf => by
      refine ⟨?_, ?_, ?_⟩
      · rw [hf.1 _ (by rw [hl]; simp) l0]
        exact Nat.beq_refl _
      · rw [hf.1 _ (by rw [hl]; simp) l1]
        exact Nat.beq_refl _
      · rw [hf.1 _ (by rw [hl]; simp) l2]
        exact Nat.beq_refl _
  rw [Nat.eq_of_beq_eq_true hz, ← card_m22_subtype] at hc
  have : 0 < Nat.card {x : M22 // Q7 e ⇑(x : Perm (Fin 22))} := Nat.card_pos_iff.2
    ⟨⟨⟨g, hg⟩⟩, inferInstance⟩
  omega

theorem fix7_one (g : M22)
    (hg : 7 ≤ (Finset.univ.filter fun p => (g : Perm (Fin 22)) p = p).card) :
    (g : Perm (Fin 22)) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpe⟩ := cover _ hg
  refine no_Q7 hp g ⟨fun i hi h => (Finset.mem_filter.1 (hpe i hi h)).2, hg, fun h => hne ?_⟩
  exact Equiv.ext h

theorem count_fix7 :
    m22Count (fun f => 7 ≤ (Finset.univ.filter fun p => f p = p).card) = 1 := by
  rw [← card_m22_subtype]
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩, ⟨⟨1, ?_⟩⟩⟩
  · exact (fix7_one a.1 a.2).trans (fix7_one b.1 b.2).symm
  · simp

theorem count_lines :
    (∀ i : Fin 4, m22Count (fun f => ∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) =
      36) ∧
    (∀ i : Fin 4, m22Count (fun f => (∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) ∧
      ∀ p, f (f (f (f p))) = p) = 4) := by
  have c0 := count_line 0 tL0 1097729 (by decide +kernel) (by decide +kernel) wL0 0 14 15
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have c1 := count_line 1 tL1 2098433 (by decide +kernel) (by decide +kernel) wL1 0 8 10
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have c2 := count_line 2 tL2 528389 (by decide +kernel) (by decide +kernel) wL2 0 2 12
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have c3 := count_line 3 tL3 264225 (by decide +kernel) (by decide +kernel) wL3 0 5 11
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
  exacts [c0.1.trans k8165a0, c1.1.trans k8165a1, c2.1.trans k8165a2, c3.1.trans k8165a3,
    c0.2.trans k8165b0, c1.2.trans k8165b1, c2.2.trans k8165b2, c3.2.trans k8165b3]

theorem count_hep :
    ∀ k : Fin 4, m22Count (fun f => ∀ p ∈ hep k, f p ∈ hep k) = 2520 := by
  intro k
  fin_cases k
  · exact (count_pres (hep 0) 1626117 [0, 2, 12, 14, 15, 19, 20] (by decide +kernel)
      (by decide) (by decide +kernel) wL2 _ (pkw_wordPerm _) 0 2 12 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).trans k8165d0
  · exact (count_pres (hep 1) 1361953 [0, 5, 11, 14, 15, 18, 20] (by decide +kernel)
      (by decide) (by decide +kernel) wL3 _ (pkw_wordPerm _) 0 5 11 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).trans k8165d1
  · exact (count_pres (hep 2) 2626821 [0, 2, 8, 10, 12, 19, 21] (by decide +kernel)
      (by decide) (by decide +kernel) wH2 _ (pkw_wordPerm _) 0 2 8 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).trans k8165d2
  · exact (count_pres (hep 3) 2362657 [0, 5, 8, 10, 11, 18, 21] (by decide +kernel)
      (by decide) (by decide +kernel) wH3 _ (pkw_wordPerm _) 0 5 8 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).trans k8165d3

theorem count_tri :
    ∀ i : Fin 4, m22Count (fun f => ∀ p ∈ tri i, f p ∈ tri i) = 288 := by
  intro i
  fin_cases i
  · exact (count_pres (tri 0) 1097728 [14, 15, 20] (by decide +kernel) (by decide)
      (by decide +kernel) wT0 _ (pkw_wordPerm _) 14 15 20 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
      k8165e0
  · exact (count_pres (tri 1) 2098432 [8, 10, 21] (by decide +kernel) (by decide)
      (by decide +kernel) wT1 _ (pkw_wordPerm _) 8 10 21 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
      k8165e1
  · exact (count_pres (tri 2) 528388 [2, 12, 19] (by decide +kernel) (by decide)
      (by decide +kernel) wT2 _ (pkw_wordPerm _) 2 12 19 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
      k8165e2
  · exact (count_pres (tri 3) 264224 [5, 11, 18] (by decide +kernel) (by decide)
      (by decide +kernel) wT3 _ (pkw_wordPerm _) 5 11 18 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
      k8165e3

theorem facts8165 :
    (∀ i : Fin 4, m22Count (fun f => ∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) =
      36) ∧
    (∀ i : Fin 4, m22Count (fun f => (∀ p, f (ofTab (lineTab i) p) = ofTab (lineTab i) (f p)) ∧
      ∀ p, f (f (f (f p))) = p) = 4) ∧
    m22Count (fun f => 7 ≤ (Finset.univ.filter fun p => f p = p).card) = 1 ∧
    (∀ k : Fin 4, m22Count (fun f => ∀ p ∈ hep k, f p ∈ hep k) = 2520) ∧
    (∀ i : Fin 4, m22Count (fun f => ∀ p ∈ tri i, f p ∈ tri i) = 288) ∧
    hexOne ∈ hexadList ∧ hexTwo ∈ hexadList :=
  ⟨count_lines.1, count_lines.2, count_fix7, count_hep, count_tri, by decide +kernel,
    by decide +kernel⟩

end CertificateChecks.KernelLC.Witt

end
