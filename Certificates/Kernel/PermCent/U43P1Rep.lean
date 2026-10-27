module

public import Certificates.Kernel.PermCent.U43P1Run

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1 CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin Subgroup

theorem comm_of_commOK {p q : ℕ} {σ τ : Equiv.Perm (Fin 820)} (hp : PRep 820 10 p σ)
    (hq : PRep 820 10 q τ) (h : Cover.commOK p q = true) : σ * τ = τ * σ := by
  have e : pc p q = pc q p := Nat.eq_of_beq_eq_true h
  have h1 := prep_pc hp hq
  rw [e] at h1
  exact prep_eq h1 (prep_pc hq hp)

theorem ordP5_spec {p : ℕ} {σ : Equiv.Perm (Fin 820)} (hp : PRep 820 10 p σ)
    (h : ordP 5 p = true) : σ ≠ 1 ∧ σ ^ 5 = 1 := by
  rw [ordP, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun e => ?_, ?_⟩
  · rw [e] at hp
    rw [isId_of_prep hp] at h
    exact Bool.noConfusion h.1
  · have h2 := h.2
    rw [show Nat.beq 5 3 = false by decide, cond_false] at h2
    have e := eq_one_of_isId (prep_pc hp (prep_pc hp (prep_pc hp (prep_pc hp hp)))) h2
    calc σ ^ 5 = σ ^ (1 + 1 + 1 + 1 + 1) := rfl
      _ = σ * (σ * (σ * (σ * σ))) := by simp only [pow_add, pow_one, mul_assoc]
      _ = 1 := e

theorem ordP3_spec {p : ℕ} {σ : Equiv.Perm (Fin 820)} (hp : PRep 820 10 p σ)
    (h : ordP 3 p = true) : σ ≠ 1 ∧ σ ^ 3 = 1 := by
  rw [ordP, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun e => ?_, ?_⟩
  · rw [e] at hp
    rw [isId_of_prep hp] at h
    exact Bool.noConfusion h.1
  · have h2 := h.2
    rw [show Nat.beq 3 3 = true by decide, cond_true] at h2
    have e := eq_one_of_isId (prep_pc hp (prep_pc hp hp)) h2
    calc σ ^ 3 = σ ^ (1 + 1 + 1) := rfl
      _ = σ * (σ * σ) := by simp only [pow_add, pow_one, mul_assoc]
      _ = 1 := e

theorem orderOf_of_ordP {p q : ℕ} (hq : q.Prime) {σ : Equiv.Perm (Fin 820)} (h1 : σ ≠ 1)
    (hp : σ ^ q = 1) (hp' : p = q) : orderOf σ = p := by
  have : Fact q.Prime := ⟨hq⟩
  rw [hp']
  exact orderOf_eq_prime hp h1

theorem normOK_spec {CG CGI LG LT : ℕ → ℕ} {W : List ℕ} {NL : ℕ}
    (h : normOK CG CGI LG LT W NL = true) :
    ∀ a < 2, ∀ b < 2, ∃ j < NL, pc (CG a) (pc (LG b) (CGI a)) = LT j := by
  rw [normOK, Bool.and_eq_true, List.all_eq_true] at h
  intro a ha b hb
  have h1 := h.2 (2 * a + b) (List.mem_range.2 (by omega))
  rw [Bool.and_eq_true, Nat.blt_eq] at h1
  have e1 : (2 * a + b) / 2 = a := by omega
  have e2 : (2 * a + b) % 2 = b := by omega
  rw [e1, e2] at h1
  exact ⟨_, h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem image_two {α : Type*} (f : ℕ → α) : f '' {k | k < 2} = {f 0, f 1} := by
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem mem_normalizer_of_closure {gs : Set (Equiv.Perm (Fin 820))} {c : Equiv.Perm (Fin 820)}
    (h : ∀ g ∈ gs, c * g * c⁻¹ ∈ closure gs) :
    c ∈ normalizer ((closure gs : Subgroup (Equiv.Perm (Fin 820))) : Set (Equiv.Perm (Fin 820))) := by
  have hmap : (closure gs).map (MulAut.conj c).toMonoidHom ≤ closure gs := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h g hg
  exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hmap
    (by rw [card_map_of_injective (MulAut.conj c).injective]))

theorem not_mem_of_coset {H : Subgroup (Equiv.Perm (Fin 820))} {t u : Equiv.Perm (Fin 820)}
    (h : t * u⁻¹ ∈ H) (hu : u ∉ H) : t ∉ H := by
  intro ht
  apply hu
  have e : u = (t * u⁻¹)⁻¹ * t := by group
  rw [e]
  exact mul_mem (inv_mem h) ht

theorem card_cen_of {c N M : ℕ} (hc : c < 6) (hN : clsN c = N)
    (hM : N * M = 3265920) (h0 : 0 < N) :
    Nat.card ↥(psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) = M := by
  have h := (cls_facts c hc).1
  rw [hN] at h
  exact Nat.eq_of_mul_eq_mul_left h0 (h.trans hM.symm)

theorem bindsS_cen :
    gensOK cgIn CgIn.G = true ∧ gensOK gsIn KIn.G = true ∧ gensOK gsFb FFb.G = true ∧
      gensOK cgM1a CgM1a.G = true ∧ gensOK (lM1a.map (·, false)) LM1a.G = true ∧
      gensOK cgIa CgIa.G = true ∧ gensOK (lIa.map (·, false)) LIa.G = true ∧
      Nat.beq (CgIn.T 0) (pidn 820 10) = true ∧ Nat.beq (KIn.T 0) (pidn 820 10) = true ∧
      Nat.beq (FFb.T 0) (pidn 820 10) = true ∧ Nat.beq (CgM1a.T 0) (pidn 820 10) = true ∧
      Nat.beq (LM1a.T 0) (pidn 820 10) = true ∧ Nat.beq (CgIa.T 0) (pidn 820 10) = true ∧
      Nat.beq (LIa.T 0) (pidn 820 10) = true ∧
      CgIn.N = 1152 ∧ KIn.N = 288 ∧ FFb.N = 960 ∧ CgM1a.N = 720 ∧ LM1a.N = 360 ∧
      CgIa.N = 720 ∧ LIa.N = 360 ∧ CgIn.ng = 2 ∧ KIn.ng = 2 ∧ FFb.ng = 2 ∧ CgM1a.ng = 2 ∧
      LM1a.ng = 2 ∧ CgIa.ng = 2 ∧ LIa.ng = 2 := by
  obtain ⟨h, -, -, -, n4, n5, n6, n7, n8, n9, n10, -, -, -, g4, g5, g6, g7, g8, g9, g10⟩ := bindsS
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, hall⟩ := h
  have ht := List.all_eq_true.1 hall
  exact ⟨h4, h5, h6, h7, h8, h9, h10, ht _ (by simp), ht _ (by simp), ht _ (by simp),
    ht _ (by simp), ht _ (by simp), ht _ (by simp), ht _ (by simp), n4, n5, n6, n7, n8, n9, n10,
    g4, g5, g6, g7, g8, g9, g10⟩

theorem gK_mem_cen {c : ℕ} (hc : c < 6) {l : List (ℕ × Bool)} {G : ℕ → ℕ}
    (hd : ∀ x ∈ l, x.2 = false ∧ detOf x.1 = 3)
    (hp : ∀ j < l.length, PRep 820 10 (G j) (gK l j)) {k : ℕ} (hk : k < l.length)
    (hcm : Cover.commOK (G k) (clsT c (clsR c)) = true) :
    gK l k ∈ psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) := by
  refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr
    (comm_of_commOK (hp k hk) (root_prep c hc) hcm)⟩
  have h := hd _ (getD_mem hk)
  unfold gK
  rw [h.1]
  exact eK_mem_range h.2

theorem pair_facts {c NC NK ngC ngK LC KC LK KK : ℕ}
    {lC lK : List (ℕ × Bool)} {GC GIC TC EC DC SC GK TK EK DK SK : ℕ → ℕ} {psC psK W : List ℕ}
    (hc : c < 6) (hgC : gensOK lC GC = true) (hgK : gensOK lK GK = true)
    (hdC : ∀ x ∈ lC, x.2 = false ∧ detOf x.1 = 3) (hdK : ∀ x ∈ lK, x.2 = false ∧ detOf x.1 = 3)
    (hnC : ngC = lC.length) (hnK : ngK = lK.length) (h2C : ngC = 2) (h2K : ngK = 2)
    (hclC : ∀ i, i < LC * KC → closPtL 820 10 ngC NC GC TC EC i = true)
    (htrC : ∀ i, i < LC * KC → treePt ngC NC 0 EC DC i = true) (hNLC : NC ≤ LC * KC)
    (h0C : Nat.beq (TC 0) (pidn 820 10) = true) (hpsC : ∀ p ∈ psC, p < 820)
    (hKC : distinctK NC (fun i => pkeyK 820 10 psC (TC i)) SC = true)
    (hclK : ∀ i, i < LK * KK → closPtL 820 10 ngK NK GK TK EK i = true)
    (htrK : ∀ i, i < LK * KK → treePt ngK NK 0 EK DK i = true) (hNLK : NK ≤ LK * KK)
    (h0K : Nat.beq (TK 0) (pidn 820 10) = true) (hpsK : ∀ p ∈ psK, p < 820)
    (hKK : distinctK NK (fun i => pkeyK 820 10 psK (TK i)) SK = true)
    (hhC : headK 820 10 ngC GC GIC = true)
    (hcom : ∀ j < 2, Cover.commOK (GC j) (clsT c (clsR c)) = true ∧
      Cover.commOK (GK j) (clsT c (clsR c)) = true)
    (hnorm : normOK GC GIC GK TK W NK = true)
    (hcard : Nat.card ↥(psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) = NC)
    (hNC : 0 < NC) (hNK : 0 < NK) :
    closure (gK lC '' {k | k < 2}) = psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) ∧
      closure (gK lK '' {k | k < 2}) ≤
        psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) ∧
      psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) ≤
        normalizer ((closure (gK lK '' {k | k < 2}) : Subgroup (Equiv.Perm (Fin 820))) :
          Set (Equiv.Perm (Fin 820))) ∧
      Nat.card (closure (gK lK '' {k | k < 2})) = NK ∧
      (∀ i < NK, ∃ y ∈ closure (gK lK '' {k | k < 2}), PRep 820 10 (TK i) y) ∧
      (∀ y ∈ closure (gK lK '' {k | k < 2}), ∃ i < NK, PRep 820 10 (TK i) y) ∧
      ∀ i < NC, ∃ y ∈ closure (gK lC '' {k | k < 2}), PRep 820 10 (TC i) y := by
  subst h2C h2K
  have hdC' : ∀ x ∈ lC, detOf x.1 ≠ 0 := fun x hx => by rw [(hdC x hx).2]; norm_num
  have hdK' : ∀ x ∈ lK, detOf x.1 ≠ 0 := fun x hx => by rw [(hdK x hx).2]; norm_num
  obtain ⟨cardC, -, ptsC⟩ := enum_group hgC hdC' hnC hclC htrC hNLC hNC h0C hpsC hKC
  obtain ⟨cardK, allK, ptsK⟩ := enum_group hgK hdK' hnK hclK htrK hNLK hNK h0K hpsK hKK
  have pC := prep_gensOK hgC hdC'
  have pK := prep_gensOK hgK hdK'
  have hCle : closure (gK lC '' {k | k < 2}) ≤
      psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact gK_mem_cen hc hdC pC (by rw [← hnC]; exact hk) (hcom k hk).1
  have hKle : closure (gK lK '' {k | k < 2}) ≤
      psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact gK_mem_cen hc hdK pK (by rw [← hnK]; exact hk) (hcom k hk).2
  have hCeq : closure (gK lC '' {k | k < 2}) =
      psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) :=
    eq_of_le_of_card_ge hCle (by rw [cardC, hcard])
  refine ⟨hCeq, hKle, ?_, cardK, ptsK, allK, ptsC⟩
  rw [← hCeq, closure_le]
  rintro _ ⟨a, ha, rfl⟩
  have haC : a < lC.length := by rw [← hnC]; exact ha
  have hGI : PRep 820 10 (GIC a) (gK lC a)⁻¹ :=
    prep_inv (pC a haC) ((headK_spec hhC).2 a ha).2.2
  refine mem_normalizer_of_closure ?_
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨j, hj, e⟩ := normOK_spec hnorm a ha b hb
  have hp := prep_pc (pC a haC) (prep_pc (pK b (by rw [← hnK]; exact hb)) hGI)
  rw [e] at hp
  obtain ⟨y, hy, hpy⟩ := ptsK j hj
  rw [mul_assoc, prep_eq hp hpy]
  exact hy

theorem card_cen0 :
    Nat.card ↥(psi.range ⊓ centralizer ({tRep 0} : Set (Equiv.Perm (Fin 820)))) = 1152 :=
  card_cen_of (N := 2835) (by norm_num) bindsC.2.1 (by norm_num) (by norm_num)

theorem card_cen1 :
    Nat.card ↥(psi.range ⊓ centralizer ({tRep 1} : Set (Equiv.Perm (Fin 820)))) = 720 :=
  card_cen_of (N := 4536) (by norm_num) bindsC.2.2.1 (by norm_num) (by norm_num)

theorem card_cen2 :
    Nat.card ↥(psi.range ⊓ centralizer ({tRep 2} : Set (Equiv.Perm (Fin 820)))) = 6048 :=
  card_cen_of (N := 540) (by norm_num) bindsC.2.2.2.1 (by norm_num) (by norm_num)

theorem card_cen3 :
    Nat.card ↥(psi.range ⊓ centralizer ({tRep 3} : Set (Equiv.Perm (Fin 820)))) = 576 :=
  card_cen_of (N := 5670) (by norm_num) bindsC.2.2.2.2.1 (by norm_num) (by norm_num)

theorem card_cen4 :
    Nat.card ↥(psi.range ⊓ centralizer ({tRep 4} : Set (Equiv.Perm (Fin 820)))) = 25920 :=
  card_cen_of (N := 126) (by norm_num) bindsC.2.2.2.2.2.1 (by norm_num) (by norm_num)

theorem card_cen5 :
    Nat.card ↥(psi.range ⊓ centralizer ({tRep 5} : Set (Equiv.Perm (Fin 820)))) = 720 :=
  card_cen_of (N := 4536) (by norm_num) bindsC.2.2.2.2.2.2.1 (by norm_num) (by norm_num)

theorem rep_In (Aut : Subgroup (Equiv.Perm (Fin 820))) :
    RepFacts psi.range Aut (tRep 0) := by
  obtain ⟨g1, g2, -, -, -, -, -, z1, z2, -, -, -, -, -, n1, n2, -, -, -, -, -, e1, e2, -⟩ :=
    bindsS_cen
  have hs := small
  rw [Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨hcm, hnm⟩ := hs
  obtain ⟨-, hKle, hnorm, hKcard, -, -, -⟩ := pair_facts (c := 0) (lC := cgIn) (lK := gsIn)
    (by norm_num) g1 g2 (by decide) (by decide) (by rw [e1]; rfl) (by rw [e2]; rfl) e1 e2
    CgIn.cl CgIn.tr (by decide) z1 baseL_lt CgIn.k KIn.cl KIn.tr (by decide) z2 baseL_lt KIn.k
    CgIn.h (fun j hj => by
      have h := hcm j (List.mem_range.2 hj)
      rw [Bool.and_eq_true] at h
      exact h) hnm (by rw [card_cen0, n1]) (by rw [n1]; norm_num) (by rw [n2]; norm_num)
  refine RepFacts.small _ hKle hnorm (by rw [hKcard, n2]) ⟨2, ?_⟩ (by rw [card_cen0]; norm_num)
  have h1 := relIndex_mul_card_of_le hKle
  rw [hKcard, n2, card_cen0] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 288) (h1.trans (by norm_num))

theorem tRep2_not_mem : tRep 2 ∉ psi.range := by
  have hs : USpec (repOf 2).1 6 := detOf_spec (k := (repOf 2).1) (by decide)
  have h : tRep 2 * uM1⁻¹ ∈ psi.range := eK_coset hs spec_cM1 (repOf 2).2
  exact not_mem_of_coset h run_M1.2.1

theorem tRep3_not_mem : tRep 3 ∉ psi.range := by
  have hs : USpec (repOf 3).1 3 := detOf_spec (k := (repOf 3).1) (by decide)
  have h : tRep 3 * uF⁻¹ ∈ psi.range := eK_coset hs cI_spec (repOf 3).2
  exact not_mem_of_coset h run_F.2.1

theorem tRep4_not_mem : tRep 4 ∉ psi.range := by
  have hs : USpec (repOf 4).1 3 := detOf_spec (k := (repOf 4).1) (by decide)
  have h : tRep 4 * uF⁻¹ ∈ psi.range := eK_coset hs cI_spec (repOf 4).2
  exact not_mem_of_coset h run_F.2.1

theorem rep_M1b (Aut : Subgroup (Equiv.Perm (Fin 820))) :
    RepFacts psi.range Aut (tRep 2) :=
  RepFacts.noA6 tRep2_not_mem fun L hL hc _ =>
    no360_of_not_dvd (by rw [card_cen2]; norm_num) L hL hc

theorem rep_Fa (Aut : Subgroup (Equiv.Perm (Fin 820))) :
    RepFacts psi.range Aut (tRep 3) :=
  RepFacts.noA6 tRep3_not_mem fun L hL hc _ =>
    no360_of_not_dvd (by rw [card_cen3]; norm_num) L hL hc

theorem rep_Fb (Aut : Subgroup (Equiv.Perm (Fin 820))) :
    RepFacts psi.range Aut (tRep 4) := by
  obtain ⟨-, -, g3, -, -, -, -, -, -, z3, -, -, -, -, -, -, n3, -, -, -, -, -, -, e3, -⟩ :=
    bindsS_cen
  have hd : ∀ x ∈ gsFb, x.2 = false ∧ detOf x.1 = 3 := by decide
  have hd' : ∀ x ∈ gsFb, detOf x.1 ≠ 0 := fun x hx => by rw [(hd x hx).2]; norm_num
  obtain ⟨cardF, -, -⟩ := enum_group g3 hd' (by rw [e3]; rfl) FFb.cl FFb.tr (by decide)
    (by rw [n3]; norm_num) z3 baseL_lt FFb.k
  rw [e3, n3] at cardF
  have pF := prep_gensOK g3 hd'
  have hf := five
  rw [List.all_eq_true] at hf
  refine RepFacts.noA6 tRep4_not_mem fun L hL hc hN => no360_of_five (gs := gK gsFb '' {k | k < 2})
    ?_ (by rw [cardF]; norm_num) (Or.inr (by rw [card_cen4]; norm_num)) L hL hc hN
  rintro _ ⟨k, hk, rfl⟩
  have h := hf k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at h
  have hk' : k < gsFb.length := by
    have : gsFb.length = 2 := rfl
    have hk2 : k < 2 := hk
    omega
  exact ⟨gK_mem_cen (by norm_num) hd pF hk' h.1, (ordP5_spec (pF k hk') h.2).2⟩

@[expose] def yA : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def yB : Equiv.Perm (Fin 6) :=
  Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def yK (k : ℕ) : Equiv.Perm (Fin 6) := if k = 0 then yA else yB

theorem yK_spec : ∀ k < 2, ∀ i : Fin 6, (yK k i : ℕ) = (a6Gens.getD k []).getD i 0 := by
  decide

theorem prep_y6OK {ys : List ℕ} {y : Equiv.Perm (Fin 6)} {p : ℕ}
    (hy : ∀ i : Fin 6, (y i : ℕ) = ys.getD i 0) (h : y6OK ys p = true) : PRep 6 3 p y := by
  intro x
  rw [y6OK, List.all_eq_true] at h
  rw [hy x]
  exact Nat.eq_of_beq_eq_true (h x (List.mem_range.2 x.2))

theorem odd_yA : Odd (orderOf yA) := by
  have h : orderOf yA = 3 := orderOf_eq_prime (p := 3) (by decide) (by decide)
  rw [h]
  decide

theorem odd_yB : Odd (orderOf yB) := by
  have h : orderOf yB = 5 := orderOf_eq_prime (p := 5) (by decide) (by decide)
  rw [h]
  decide

theorem card_y6 : Nat.card (closure ({yA, yB} : Set (Equiv.Perm (Fin 6)))) = 360 := by
  obtain ⟨hb, -, -, n6, -, -, g6⟩ := bindsD
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, y0⟩, y1⟩, -⟩, -⟩, z6⟩ := hb
  have hg : ∀ k < Y6.ng, PRep 6 3 (Y6.G k) (yK k) := by
    intro k hk
    rw [g6] at hk
    interval_cases k
    · exact prep_y6OK (yK_spec 0 (by norm_num)) y0
    · exact prep_y6OK (yK_spec 1 (by norm_num)) y1
  obtain ⟨hcard, -⟩ := group_facts (n := 6) (w := 3) (by norm_num) (by norm_num) hg
    (fun i hi => Y6.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => Y6.tr i (lt_of_lt_of_le hi (by decide))) (by rw [n6]; norm_num)
    (Nat.eq_of_beq_eq_true z6) (by decide) Y6.k
  rw [g6, image_two, n6] at hcard
  exact hcard

theorem pairHom_castAdd {x : Equiv.Perm (Fin 820)} {y : Equiv.Perm (Fin 6)} (j : Fin 820) :
    (pairHom 820 (x, y) (Fin.castAdd 6 j) : ℕ) = x j := by
  change (finSumFinEquiv (Equiv.Perm.sumCongr x y (finSumFinEquiv.symm (Fin.castAdd 6 j))) :
    Fin (820 + 6)).val = _
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.Perm.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.val_castAdd]

theorem pairHom_natAdd {x : Equiv.Perm (Fin 820)} {y : Equiv.Perm (Fin 6)} (j : Fin 6) :
    (pairHom 820 (x, y) (Fin.natAdd 820 j) : ℕ) = y j + 820 := by
  change (finSumFinEquiv (Equiv.Perm.sumCongr x y (finSumFinEquiv.symm (Fin.natAdd 820 j))) :
    Fin (820 + 6)).val = _
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.Perm.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.val_natAdd, add_comm]

theorem prep_dgOK {k : ℕ} {ys : List ℕ} {y : Equiv.Perm (Fin 6)} {p : ℕ}
    (hk : (matK k).det ≠ 0) (hy : ∀ i : Fin 6, (y i : ℕ) = ys.getD i 0) (h : dgOK k ys p = true) :
    PRep (820 + 6) 10 p (pairHom 820 (eK k false, y)) := by
  intro x
  rw [dgOK, List.all_eq_true] at h
  have h1 := Nat.eq_of_beq_eq_true (h x (List.mem_range.2 x.2))
  rw [h1]
  by_cases hin : (x : ℕ) < 820
  · have hb : Nat.blt x 820 = true := by
      rw [Nat.blt_eq]
      exact hin
    have he : x = Fin.castAdd 6 ⟨x, hin⟩ := rfl
    rw [hb, cond_true]
    conv_rhs => rw [he]
    rw [pairHom_castAdd]
    exact (eK_apply hk ⟨x, hin⟩).symm
  · have hb : Nat.blt x 820 = false := by
      cases e : Nat.blt (x : ℕ) 820
      · rfl
      · rw [Nat.blt_eq] at e
        exact absurd e hin
    have hj : (x : ℕ) - 820 < 6 := by
      have := x.2
      omega
    have he : x = Fin.natAdd 820 ⟨(x : ℕ) - 820, hj⟩ :=
      Fin.ext (by simp only [Fin.val_natAdd]; omega)
    have hyv : ys.getD ((x : ℕ) - 820) 0 = (y ⟨(x : ℕ) - 820, hj⟩ : ℕ) := (hy ⟨_, hj⟩).symm
    rw [hb, cond_false, hyv]
    conv_rhs => rw [he]
    rw [pairHom_natAdd]

theorem baseD_lt : ∀ p ∈ baseD, p < 826 := by decide

theorem a6_core {c : ℕ} {lK : List (ℕ × Bool)} {codes : List ℕ} {GK : ℕ → ℕ}
    {Dng DN DL DKk : ℕ} {DG DT DE DD DS : ℕ → ℕ}
    (hKle : closure (gK lK '' {k | k < 2}) ≤
      psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))))
    (hLcard : Nat.card (closure (gK lK '' {k | k < 2})) = 360)
    (hCcard : Nat.card ↥(psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) = 720)
    (hgK : ∀ j < 2, PRep 820 10 (GK j) (gK lK j)) (h3 : ordP 3 (GK 0) = true)
    (h5 : ordP 5 (GK 1) = true) (hcode : ∀ k < 2, gK lK k = eK (codes.getD k 0) false)
    (hdk : ∀ k < 2, detOf (codes.getD k 0) ≠ 0)
    (hdg : ∀ k < 2, dgOK (codes.getD k 0) (a6Gens.getD k []) (DG k) = true) (hDng : Dng = 2)
    (hDcl : ∀ i, i < DL * DKk → closPtL 826 10 Dng DN DG DT DE i = true)
    (hDtr : ∀ i, i < DL * DKk → treePt Dng DN 0 DE DD i = true) (hDNL : DN ≤ DL * DKk)
    (hDN : DN = 360) (hD0 : Nat.beq (DT 0) (pidn 826 10) = true)
    (hDK : distinctK DN (fun i => pkeyK 826 10 baseD (DT i)) DS = true) :
    (∃ a, (closure (gK lK '' {k | k < 2})).relIndex
        (psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) = 2 ^ a) ∧
      closure (gK lK '' {k | k < 2}) ≤
        CFSG.ComponentClassification.HarrisLit.Q81.oddPart (psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) ∧
      Nonempty (↥(closure (gK lK '' {k | k < 2})) ≃* alternatingGroup (Fin 6)) := by
  have o0 := ordP3_spec (hgK 0 (by norm_num)) h3
  have o1 := ordP5_spec (hgK 1 (by norm_num)) h5
  have ord0 : orderOf (gK lK 0) = 3 := orderOf_of_ordP Nat.prime_three o0.1 o0.2 rfl
  have ord1 : orderOf (gK lK 1) = 5 := orderOf_of_ordP Nat.prime_five o1.1 o1.2 rfl
  refine ⟨⟨1, ?_⟩, closure_le_oddPart ?_, ?_⟩
  · have h1 := relIndex_mul_card_of_le hKle
    rw [hLcard, hCcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (h1.trans (by norm_num))
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨hKle (subset_closure ⟨k, hk, rfl⟩), ?_⟩
    have hk2 : k < 2 := hk
    interval_cases k
    · rw [ord0]
      decide
    · rw [ord1]
      decide
  · have hg : ∀ k < Dng, PRep (820 + 6) 10 (DG k) (pairHom 820 (gK lK k, yK k)) := by
      intro k hk
      rw [hDng] at hk
      rw [hcode k hk]
      exact prep_dgOK (detOf_spec (hdk k hk)).1 (yK_spec k hk) (hdg k hk)
    obtain ⟨hD, -⟩ := group_facts (n := 820 + 6) (w := 10) (by norm_num) (by norm_num) hg
      (fun i hi => hDcl i (lt_of_lt_of_le hi hDNL)) (fun i hi => hDtr i (lt_of_lt_of_le hi hDNL))
      (by rw [hDN]; norm_num) (Nat.eq_of_beq_eq_true hD0) baseD_lt hDK
    rw [hDng, image_two, hDN] at hD
    have e0 : yK 0 = yA := rfl
    have e1 : yK 1 = yB := rfl
    simp only [e0, e1] at hD
    have hX : Nat.card (closure ({gK lK 0, gK lK 1} : Set (Equiv.Perm (Fin 820)))) = 360 := by
      rw [← image_two (gK lK)]
      exact hLcard
    rw [image_two (gK lK)]
    exact nonempty_equiv_alternating_six_of_card odd_yA odd_yB card_y6 hX hD

end CertificateChecks.KernelPermCent.U43P1

end
