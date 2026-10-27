module

public import Certificates.Kernel.PermCent.U43P1Grp
public import Certificates.Kernel.PermCent.U43P1Cov
public import Certificates.Kernel.PermCent.U43P1BindS

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1 CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin Subgroup

@[expose] noncomputable def gK (l : List (ℕ × Bool)) (j : ℕ) : Equiv.Perm (Fin 820) :=
  eK (l.getD j (0, false)).1 (l.getD j (0, false)).2

theorem getD_mem {l : List (ℕ × Bool)} {j : ℕ} (hj : j < l.length) :
    l.getD j (0, false) ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem prep_gensOK {l : List (ℕ × Bool)} {G : ℕ → ℕ} (h : gensOK l G = true)
    (hd : ∀ x ∈ l, detOf x.1 ≠ 0) : ∀ j < l.length, PRep 820 10 (G j) (gK l j) := by
  intro j hj
  rw [gensOK, List.all_eq_true] at h
  exact prep_matOK (detOf_spec (hd _ (getD_mem hj))).1 (h j (List.mem_range.2 hj))

abbrev USpec (k d : ℕ) : Prop :=
  (matK k).det ≠ 0 ∧ IsUnitaryF (glK k) ∧ (glK k : Matrix (Fin 4) (Fin 4) F9).det = uncode d

theorem cI_spec : USpec cI 3 := by
  have h1 : (matK cI).det = uncode 3 := by decide +kernel
  have h0 : (matK cI).det ≠ 0 := by
    rw [h1]
    decide
  exact ⟨h0, isUnitaryF_glK h0 (by decide +kernel), by rw [glK_val h0, h1]⟩

theorem prep_pk' {k d : ℕ} (hs : USpec k d) (ε : Bool) : PRep 820 10 (pk k ε) (eK k ε) :=
  prep_pk hs.1

theorem eK_mem_normalizer' {k d : ℕ} (hs : USpec k d) (ε : Bool) :
    eK k ε ∈ normalizer (psi.range : Set (Equiv.Perm (Fin 820))) :=
  perm820_frob_mem_normalizer hs.2.1 (Bool.toNat_le ε)

theorem eK_coset {k k₀ d : ℕ} (hs : USpec k d) (hs₀ : USpec k₀ d) (ε : Bool) :
    eK k ε * (eK k₀ ε)⁻¹ ∈ psi.range :=
  mem_coset hs.2.1 hs₀.2.1 (by rw [hs.2.2, hs₀.2.2]) ε.toNat

theorem gK_mem_or {l : List (ℕ × Bool)} {k₀ d₀ : ℕ} {ε₀ : Bool} (hs : USpec k₀ d₀)
    (h : ∀ x ∈ l, detOf x.1 ≠ 0 ∧ ((x.2 = false ∧ detOf x.1 = 3) ∨ (x.2 = ε₀ ∧ detOf x.1 = d₀))) :
    ∀ j < l.length, gK l j ∈ psi.range ∨ gK l j * (eK k₀ ε₀)⁻¹ ∈ psi.range := by
  intro j hj
  obtain ⟨hd, h2⟩ := h _ (getD_mem hj)
  have hsj : USpec (l.getD j (0, false)).1 (detOf (l.getD j (0, false)).1) := detOf_spec hd
  unfold gK
  rcases h2 with ⟨he, h3⟩ | ⟨he, h3⟩
  · rw [he]
    exact Or.inl (eK_mem_range h3)
  · rw [he]
    rw [h3] at hsj
    exact Or.inr (eK_coset hsj hs ε₀)

theorem mem_sup_of_coset {H : Subgroup (Equiv.Perm (Fin 820))} {σ u : Equiv.Perm (Fin 820)}
    (h : σ ∈ H ∨ σ * u⁻¹ ∈ H) : σ ∈ H ⊔ zpowers u := by
  rcases h with h | h
  · exact mem_sup_left h
  · have e : σ = σ * u⁻¹ * u := by group
    rw [e]
    exact mul_mem (mem_sup_left h) (mem_sup_right (mem_zpowers u))

theorem enum_group {l : List (ℕ × Bool)} {ng N L K : ℕ} {G T E D S : ℕ → ℕ} {ps : List ℕ}
    (hG : gensOK l G = true) (hd : ∀ x ∈ l, detOf x.1 ≠ 0) (hng : ng = l.length)
    (hcl : ∀ i, i < L * K → closPtL 820 10 ng N G T E i = true)
    (htr : ∀ i, i < L * K → treePt ng N 0 E D i = true) (hNL : N ≤ L * K) (hN : 0 < N)
    (h0 : Nat.beq (T 0) (pidn 820 10) = true) (hps : ∀ p ∈ ps, p < 820)
    (hK : distinctK N (fun i => pkeyK 820 10 ps (T i)) S = true) :
    Nat.card (closure (gK l '' {k | k < ng})) = N ∧
      (∀ y ∈ closure (gK l '' {k | k < ng}), ∃ i < N, PRep 820 10 (T i) y) ∧
      ∀ i < N, ∃ y ∈ closure (gK l '' {k | k < ng}), PRep 820 10 (T i) y :=
  group_facts (by norm_num) (by norm_num) (fun k hk => prep_gensOK hG hd k (hng ▸ hk))
    (fun i hi => hcl i (lt_of_lt_of_le hi hNL)) (fun i hi => htr i (lt_of_lt_of_le hi hNL)) hN
    (Nat.eq_of_beq_eq_true h0) hps hK

@[expose] def repsOf (cs : List ℕ) : Set (Equiv.Perm (Fin 820)) := {t | ∃ c ∈ cs, t = tRep c}

theorem root_prep : ∀ c < 6, PRep 820 10 (clsT c (clsR c)) (tRep c) := by
  obtain ⟨hb, -⟩ := bindsC
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, tIn⟩, -⟩, -⟩, tM1a⟩, -⟩, -⟩, tM1b⟩, -⟩, -⟩,
    tFa⟩, -⟩, -⟩, tFb⟩, -⟩, -⟩, tIa⟩ := hb
  intro c hc
  interval_cases c
  · exact prep_root 0 (by norm_num) tIn
  · exact prep_root 1 (by norm_num) tM1a
  · exact prep_root 2 (by norm_num) tM1b
  · exact prep_root 3 (by norm_num) tFa
  · exact prep_root 4 (by norm_num) tFb
  · exact prep_root 5 (by norm_num) tIa

theorem eq_conj_of_cls {c j : ℕ} (hc : c < 6) (hj : j < clsN c)
    {σ : Equiv.Perm (Fin 820)} (hσ : PRep 820 10 (clsT c j) σ) :
    ∃ h ∈ psi.range, σ = h * tRep c * h⁻¹ := by
  obtain ⟨-, hreach, -⟩ := cls_facts c hc
  obtain ⟨h, hh, hp⟩ := hreach j hj
  exact ⟨h, hh, prep_eq hσ hp⟩

theorem mul_self_of_orderOf {σ : Equiv.Perm (Fin 820)} (h : orderOf σ = 2) :
    σ * σ = 1 ∧ σ ≠ 1 := by
  refine ⟨by rw [← sq, ← h, pow_orderOf_eq_one], fun e => ?_⟩
  rw [e, orderOf_one] at h
  exact absurd h (by norm_num)

theorem lookOK_spec {u : ℕ} {cls : ℕ → ℕ → ℕ} {sz : ℕ → ℕ} {cs : List ℕ} {rs : List (ℕ × ℕ)}
    {W : List ℕ} (h : lookOK u cls sz cs rs W = true) :
    ∀ x ∈ rs, ∃ c ∈ cs, ∃ j < sz c, cls c j = pc u (pc (cls x.1 x.2) u) := by
  rw [lookOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hl, h⟩ := h
  have hl' : rs.length = W.length := Nat.eq_of_beq_eq_true hl
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hz : i < (rs.zip W).length := by
    rw [List.length_zip]
    omega
  have h1 := h _ (List.getElem_mem hz)
  rw [List.getElem_zip] at h1
  obtain ⟨hc, hj, he⟩ := inCls_spec h1
  exact ⟨_, hc, _, hj, he⟩

theorem run_cover {U : Equiv.Perm (Fin 820)} {pu : ℕ}
    {S : Subgroup (Equiv.Perm (Fin 820))} {ST : ℕ → ℕ} {cs W LK : List ℕ}
    (hU : U ∈ normalizer (psi.range : Set (Equiv.Perm (Fin 820)))) (hpu : PRep 820 10 pu U)
    (hUU : U * U = 1) (hS : Nat.card S = 256) (hSle : S ≤ psi.range ⊔ zpowers U)
    (hpts : ∀ s ∈ S, ∃ i < 256, PRep 820 10 (ST i) s)
    (hcov : coverOK ST clsT clsN cs W = true) (hW : W.length = 256) (hcs : ∀ c ∈ cs, c < 6)
    (hlk : lookOK pu clsT clsN cs (cs.map fun c => (c, clsR c)) LK = true) :
    U ∉ psi.range ∧ ∀ τ ∈ psi.range ⊔ zpowers U, orderOf τ = 2 →
      ∃ t ∈ repsOf cs, ∃ g ∈ psi.range, τ = g * t * g⁻¹ := by
  have hUU' : U * U ∈ psi.range := hUU ▸ one_mem _
  have h256 : 256 ∣ Nat.card ↥(psi.range ⊔ zpowers U) := hS ▸ card_dvd_of_le hSle
  have hUA : U ∉ psi.range := by
    intro h
    rw [sup_eq_left.2 ((zpowers_le).2 h), card_range_psi'] at h256
    norm_num at h256
  have hcard : Nat.card ↥(psi.range ⊔ zpowers U) = 2 * 3265920 := by
    rw [card_sup_zpowers_of_sq_mem hU hUU' hUA, card_range_psi']
  refine ⟨hUA, cover_of_sylow hU hSle (by rw [hS, hcard, factorization_two]; norm_num) ?_ ?_⟩
  · intro s hs hs2
    obtain ⟨i, hi, hp⟩ := hpts s hs
    obtain ⟨c, hc, j, hj, e⟩ := coverOK_spec hcov i (by rw [hW]; exact hi)
      ((invol_iff hp).2 (mul_self_of_orderOf hs2))
    rw [← e] at hp
    obtain ⟨h, hh, he⟩ := eq_conj_of_cls (hcs c hc) hj hp
    exact ⟨tRep c, ⟨c, hc, rfl⟩, h, hh, he⟩
  · rintro t ⟨c, hc, rfl⟩
    obtain ⟨c', hc', j, hj, e⟩ := lookOK_spec hlk (c, clsR c) (List.mem_map_of_mem hc)
    have e' : clsT c' j = pc pu (pc (clsT c (clsR c)) pu) := e
    have hp := prep_pc hpu (prep_pc (root_prep c (hcs c hc)) hpu)
    rw [← e'] at hp
    obtain ⟨h, hh, he⟩ := eq_conj_of_cls (hcs c' hc') hj hp
    refine ⟨tRep c', ⟨c', hc', rfl⟩, h, hh, ?_⟩
    rw [← he, inv_eq_of_mul_eq_one_right hUU, mul_assoc]

theorem run_facts {k₀ d₀ : ℕ} {ε₀ : Bool}
    {l : List (ℕ × Bool)} {ng N L K : ℕ} {G T E D S : ℕ → ℕ} {cs W LK : List ℕ}
    (hs : USpec k₀ d₀) (hid : isId (pc (pk k₀ ε₀) (pk k₀ ε₀)) = true)
    (hG : gensOK l G = true)
    (hl : ∀ x ∈ l, detOf x.1 ≠ 0 ∧ ((x.2 = false ∧ detOf x.1 = 3) ∨ (x.2 = ε₀ ∧ detOf x.1 = d₀)))
    (hng : ng = l.length) (hcl : ∀ i, i < L * K → closPtL 820 10 ng N G T E i = true)
    (htr : ∀ i, i < L * K → treePt ng N 0 E D i = true) (hNL : N ≤ L * K) (hN : N = 256)
    (h0 : Nat.beq (T 0) (pidn 820 10) = true)
    (hK : distinctK N (fun i => pkeyK 820 10 baseL4 (T i)) S = true)
    (hcov : coverOK T clsT clsN cs W = true) (hW : W.length = 256) (hcs : ∀ c ∈ cs, c < 6)
    (hlk : lookOK (pk k₀ ε₀) clsT clsN cs (cs.map fun c => (c, clsR c)) LK = true) :
    eK k₀ ε₀ * eK k₀ ε₀ = 1 ∧ eK k₀ ε₀ ∉ psi.range ∧
      ∀ τ ∈ psi.range ⊔ zpowers (eK k₀ ε₀), orderOf τ = 2 →
        ∃ t ∈ repsOf cs, ∃ g ∈ psi.range, τ = g * t * g⁻¹ := by
  have hpu := prep_pk' hs ε₀
  have hUU : eK k₀ ε₀ * eK k₀ ε₀ = 1 := eq_one_of_isId (prep_pc hpu hpu) hid
  subst hN
  obtain ⟨hcard, hpts, -⟩ := enum_group hG (fun x hx => (hl x hx).1) hng hcl htr hNL
    (by norm_num) h0 baseL4_lt hK
  have hSle : closure (gK l '' {k | k < ng}) ≤ psi.range ⊔ zpowers (eK k₀ ε₀) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact mem_sup_of_coset (gK_mem_or hs hl k (hng ▸ hk))
  exact ⟨hUU, run_cover (eK_mem_normalizer' hs ε₀) hpu hUU hcard hSle hpts hcov hW hcs hlk⟩

theorem spec_cM1 : USpec cM1 6 := detOf_spec (k := cM1) (by decide)

theorem spec_cDi : USpec cDi 1 := detOf_spec (k := cDi) (by decide)

theorem spec_cDmi : USpec cDmi 2 := detOf_spec (k := cDmi) (by decide)

theorem look_parts :
    isId (pc (pk cM1 false) (pk cM1 false)) = true ∧ isId (pc (pk cI true) (pk cI true)) = true ∧
      isId (pc (pk cDi true) (pk cDi true)) = true ∧
      lookOK (pk cM1 false) clsT clsN [0, 1, 2] ([0, 1, 2].map fun c => (c, clsR c)) lkM1 = true ∧
      lookOK (pk cI true) clsT clsN [0, 3, 4] ([0, 3, 4].map fun c => (c, clsR c)) lkF = true ∧
      lookOK (pk cDi true) clsT clsN [0, 5] ([0, 5].map fun c => (c, clsR c)) lkI = true := by
  have h := look
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem cover_parts :
    coverOK SM1.T clsT clsN [0, 1, 2] covM1 = true ∧ coverOK SF.T clsT clsN [0, 3, 4] covF = true ∧
      coverOK SI.T clsT clsN [0, 5] covI = true ∧
      covM1.length = 256 ∧ covF.length = 256 ∧ covI.length = 256 := by
  obtain ⟨h, h1, h2, h3⟩ := cover
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2, h1, h2, h3⟩

theorem bindsS_parts :
    gensOK sylM1 SM1.G = true ∧ gensOK sylF SF.G = true ∧ gensOK sylI SI.G = true ∧
      Nat.beq (SM1.T 0) (pidn 820 10) = true ∧ Nat.beq (SF.T 0) (pidn 820 10) = true ∧
      Nat.beq (SI.T 0) (pidn 820 10) = true ∧ SM1.N = 256 ∧ SF.N = 256 ∧ SI.N = 256 ∧
      SM1.ng = 4 ∧ SF.ng = 4 ∧ SI.ng = 3 := by
  obtain ⟨h, n1, n2, n3, -, -, -, -, -, -, -, g1, g2, g3, -⟩ := bindsS
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hall⟩ := h
  have ht := List.all_eq_true.1 hall
  exact ⟨h1, h2, h3, ht _ (by simp), ht _ (by simp), ht _ (by simp), n1, n2, n3, g1, g2, g3⟩

@[expose] noncomputable def uM1 : Equiv.Perm (Fin 820) := eK cM1 false

@[expose] noncomputable def uF : Equiv.Perm (Fin 820) := eK cI true

@[expose] noncomputable def uI : Equiv.Perm (Fin 820) := eK cDi true

theorem run_M1 :
    uM1 * uM1 = 1 ∧ uM1 ∉ psi.range ∧ ∀ τ ∈ psi.range ⊔ zpowers uM1, orderOf τ = 2 →
      ∃ t ∈ repsOf [0, 1, 2], ∃ g ∈ psi.range, τ = g * t * g⁻¹ := by
  obtain ⟨i1, -, -, l1, -, -⟩ := look_parts
  obtain ⟨c1, -, -, w1, -, -⟩ := cover_parts
  obtain ⟨g1, -, -, z1, -, -, n1, -, -, e1, -, -⟩ := bindsS_parts
  exact run_facts (l := sylM1) spec_cM1 i1 g1 (by decide) (by rw [e1]; rfl) SM1.cl SM1.tr
    (by decide) n1 z1 SM1.k c1 w1 (by decide) l1

theorem run_F :
    uF * uF = 1 ∧ uF ∉ psi.range ∧ ∀ τ ∈ psi.range ⊔ zpowers uF, orderOf τ = 2 →
      ∃ t ∈ repsOf [0, 3, 4], ∃ g ∈ psi.range, τ = g * t * g⁻¹ := by
  obtain ⟨-, i2, -, -, l2, -⟩ := look_parts
  obtain ⟨-, c2, -, -, w2, -⟩ := cover_parts
  obtain ⟨-, g2, -, -, z2, -, -, n2, -, -, e2, -⟩ := bindsS_parts
  exact run_facts (l := sylF) cI_spec i2 g2 (by decide) (by rw [e2]; rfl) SF.cl SF.tr
    (by decide) n2 z2 SF.k c2 w2 (by decide) l2

theorem run_I :
    uI * uI = 1 ∧ uI ∉ psi.range ∧ ∀ τ ∈ psi.range ⊔ zpowers uI, orderOf τ = 2 →
      ∃ t ∈ repsOf [0, 5], ∃ g ∈ psi.range, τ = g * t * g⁻¹ := by
  obtain ⟨-, -, i3, -, -, l3⟩ := look_parts
  obtain ⟨-, -, c3, -, -, w3⟩ := cover_parts
  obtain ⟨-, -, g3, -, -, z3, -, -, n3, -, -, e3⟩ := bindsS_parts
  exact run_facts (l := sylI) spec_cDi i3 g3 (by decide) (by rw [e3]; rfl) SI.cl SI.tr
    (by decide) n3 z3 SI.k c3 w3 (by decide) l3

@[expose] noncomputable def dK : Equiv.Perm (Fin 820) := eK cDi false

theorem dK_mem_normalizer : dK ∈ normalizer (psi.range : Set (Equiv.Perm (Fin 820))) :=
  eK_mem_normalizer' spec_cDi false

theorem d_facts : dK⁻¹ = eK cDmi false ∧ dK * uF * dK⁻¹ = eK cM1 true ∧
    dK * uI * dK⁻¹ = eK cDmi true := by
  have h := dconj
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have pd := prep_pk' spec_cDi false
  have pdm := prep_pk' spec_cDmi false
  have hinv : dK⁻¹ = eK cDmi false :=
    (inv_eq_of_mul_eq_one_right (eq_one_of_isId (prep_pc pd pdm) h1))
  refine ⟨hinv, ?_, ?_⟩
  · rw [hinv]
    have hp := prep_pc pd (prep_pc (prep_pk' cI_spec true) pdm)
    rw [Nat.eq_of_beq_eq_true h2] at hp
    rw [mul_assoc]
    exact prep_eq hp (prep_pk' spec_cM1 true)
  · rw [hinv]
    have hp := prep_pc pd (prep_pc (prep_pk' spec_cDi true) pdm)
    rw [Nat.eq_of_beq_eq_true h3] at hp
    rw [mul_assoc]
    exact prep_eq hp (prep_pk' spec_cDmi true)

theorem uncode_six : uncode 6 = -1 := by decide

theorem uncode_one : uncode 1 = iF := by decide

theorem uncode_two : uncode 2 = -iF := by decide

theorem not_invol_of_det {A : GL (Fin 4) F9} (hA : IsUnitaryF A)
    (hd : (A : Matrix (Fin 4) (Fin 4) F9).det = iF ∨ (A : Matrix (Fin 4) (Fin 4) F9).det = -iF)
    (h2 : perm820 A * perm820 A = 1) : False := by
  have hdet : ((A * A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9).det = uncode 6 := by
    rw [Units.val_mul, Matrix.det_mul]
    rcases hd with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  have hm := mem_coset (isUnitaryF_mul hA hA) spec_cM1.2.1 (by rw [hdet, spec_cM1.2.2]) 0
  rw [pow_zero, mul_one, map_mul, h2, one_mul] at hm
  apply run_M1.2.1
  have e : uM1 = (perm820 (glK cM1) * frob820 ^ 0)⁻¹⁻¹ := by
    rw [inv_inv]
    rfl
  rw [e]
  exact inv_mem hm

theorem coset_cases {A : GL (Fin 4) F9} {ε : ℕ} (hε : ε ≤ 1)
    (hA : IsUnitaryF A) (h2 : perm820 A * frob820 ^ ε * (perm820 A * frob820 ^ ε) = 1) :
    perm820 A * frob820 ^ ε ∈ psi.range ∨
      perm820 A * frob820 ^ ε * uM1⁻¹ ∈ psi.range ∨
      perm820 A * frob820 ^ ε * uF⁻¹ ∈ psi.range ∨
      perm820 A * frob820 ^ ε * uI⁻¹ ∈ psi.range ∨
      perm820 A * frob820 ^ ε * (eK cM1 true)⁻¹ ∈ psi.range ∨
      perm820 A * frob820 ^ ε * (eK cDmi true)⁻¹ ∈ psi.range := by
  rcases det_cases hA with h | h | h | h <;> interval_cases ε
  · left
    rw [pow_zero, mul_one]
    exact perm820_mem_range hA h
  · exact Or.inr (Or.inr (Or.inl
      (mem_coset hA cI_spec.2.1 (by rw [h, cI_spec.2.2, uncode_three]) 1)))
  · rw [pow_zero, mul_one] at h2
    exact (not_invol_of_det hA (Or.inl h) h2).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (mem_coset hA spec_cDi.2.1 (by rw [h, spec_cDi.2.2, uncode_one]) 1))))
  · exact Or.inr (Or.inl (mem_coset hA spec_cM1.2.1 (by rw [h, spec_cM1.2.2, uncode_six]) 0))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (mem_coset hA spec_cM1.2.1 (by rw [h, spec_cM1.2.2, uncode_six]) 1)))))
  · rw [pow_zero, mul_one] at h2
    exact (not_invol_of_det hA (Or.inr h) h2).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (mem_coset hA spec_cDmi.2.1 (by rw [h, spec_cDmi.2.2, uncode_two]) 1)))))

@[expose] def repsAll : Set (Equiv.Perm (Fin 820)) :=
  {t | ∃ c < 6, t = tRep c ∨ t = dK * tRep c * dK⁻¹}

theorem mem_repsAll_of {cs : List ℕ} (hcs : ∀ c ∈ cs, c < 6) {t : Equiv.Perm (Fin 820)}
    (ht : t ∈ repsOf cs) : t ∈ repsAll := by
  obtain ⟨c, hc, rfl⟩ := ht
  exact ⟨c, hcs c hc, Or.inl rfl⟩

theorem conj_mem_repsAll_of {cs : List ℕ} (hcs : ∀ c ∈ cs, c < 6) {t : Equiv.Perm (Fin 820)}
    (ht : t ∈ repsOf cs) : dK * t * dK⁻¹ ∈ repsAll := by
  obtain ⟨c, hc, rfl⟩ := ht
  exact ⟨c, hcs c hc, Or.inr rfl⟩

theorem cover_conj {U : Equiv.Perm (Fin 820)} {cs : List ℕ}
    (hcs : ∀ c ∈ cs, c < 6)
    (hrun : ∀ τ ∈ psi.range ⊔ zpowers U, orderOf τ = 2 →
      ∃ t ∈ repsOf cs, ∃ g ∈ psi.range, τ = g * t * g⁻¹)
    {σ : Equiv.Perm (Fin 820)} (hσ : σ * (dK * U * dK⁻¹)⁻¹ ∈ psi.range) (h2 : orderOf σ = 2) :
    ∃ t ∈ repsAll, ∃ g ∈ psi.range, σ = g * t * g⁻¹ := by
  have hdi : dK⁻¹ ∈ normalizer (psi.range : Set (Equiv.Perm (Fin 820))) :=
    inv_mem dK_mem_normalizer
  have h1 : dK⁻¹ * σ * dK * U⁻¹ ∈ psi.range := by
    have e : dK⁻¹ * σ * dK * U⁻¹ = dK⁻¹ * (σ * (dK * U * dK⁻¹)⁻¹) * dK⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp hdi _).mp hσ
  obtain ⟨t, ht, g, hg, e⟩ := hrun _ (mem_sup_of_coset (Or.inr h1)) (by rw [orderOf_conj_inv, h2])
  refine ⟨_, conj_mem_repsAll_of hcs ht, dK * g * dK⁻¹,
    (mem_normalizer_iff.mp dK_mem_normalizer g).mp hg, ?_⟩
  have e2 : σ = dK * (dK⁻¹ * σ * dK) * dK⁻¹ := by group
  rw [e2, e]
  group

theorem inv_cover {A : GL (Fin 4) F9} {ε : ℕ} (hε : ε ≤ 1)
    (hA : IsUnitaryF A) (h2 : orderOf (perm820 A * frob820 ^ ε) = 2) :
    ∃ t ∈ repsAll, ∃ g ∈ psi.range, perm820 A * frob820 ^ ε = g * t * g⁻¹ := by
  obtain ⟨-, -, hM1⟩ := run_M1
  obtain ⟨-, -, hF⟩ := run_F
  obtain ⟨-, -, hI⟩ := run_I
  obtain ⟨hdi, hdF, hdI⟩ := d_facts
  have hc1 : ∀ c ∈ [0, 1, 2], c < 6 := by decide
  have hc2 : ∀ c ∈ [0, 3, 4], c < 6 := by decide
  have hc3 : ∀ c ∈ [0, 5], c < 6 := by decide
  rcases coset_cases hε hA (mul_self_of_orderOf h2).1 with h | h | h | h | h | h
  · obtain ⟨t, ht, g, hg, e⟩ := hM1 _ (mem_sup_left h) h2
    exact ⟨t, mem_repsAll_of hc1 ht, g, hg, e⟩
  · obtain ⟨t, ht, g, hg, e⟩ := hM1 _ (mem_sup_of_coset (Or.inr h)) h2
    exact ⟨t, mem_repsAll_of hc1 ht, g, hg, e⟩
  · obtain ⟨t, ht, g, hg, e⟩ := hF _ (mem_sup_of_coset (Or.inr h)) h2
    exact ⟨t, mem_repsAll_of hc2 ht, g, hg, e⟩
  · obtain ⟨t, ht, g, hg, e⟩ := hI _ (mem_sup_of_coset (Or.inr h)) h2
    exact ⟨t, mem_repsAll_of hc3 ht, g, hg, e⟩
  · rw [← hdF] at h
    exact cover_conj hc2 hF h h2
  · rw [← hdI] at h
    exact cover_conj hc3 hI h h2

end CertificateChecks.KernelPermCent.U43P1

end
