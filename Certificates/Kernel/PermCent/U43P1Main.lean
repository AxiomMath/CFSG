module

public import Certificates.Kernel.PermCent.U43P1Cf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UBridge
public import Certificates.Kernel.PermCent.U43P1BindT

public section


namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1 CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin Subgroup
  CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def u43ModelK : AutModel X₀ 820 where
  π := psi
  inj := psi_injective
  cent _ hc := eq_one_of_commute_psi hc
  ext α := by
    obtain ⟨A, ε, -, -, h⟩ := exists_aut_form α
    exact ⟨_, h⟩

theorem spec_of {k d : ℕ} (h : detOf k = d) (hd : d ≠ 0) : USpec k d := by
  subst h
  exact detOf_spec hd

theorem coset_trans {H : Subgroup (Equiv.Perm (Fin 820))} {v w u : Equiv.Perm (Fin 820)}
    (h1 : v * u⁻¹ ∈ H) (h2 : w * u⁻¹ ∈ H) : v * w⁻¹ ∈ H := by
  have e : v * w⁻¹ = v * u⁻¹ * (w * u⁻¹)⁻¹ := by group
  rw [e]
  exact mul_mem h1 (inv_mem h2)

theorem aut_form {v : Equiv.Perm (Fin 820)} (hv : v ∈ u43ModelK.T.range) :
    ∃ (A : GL (Fin 4) F9) (ε : ℕ), ε ≤ 1 ∧ IsUnitaryF A ∧ v = perm820 A * frob820 ^ ε := by
  obtain ⟨β, rfl⟩ := hv
  obtain ⟨A, ε, hε, hA, hind⟩ := exists_aut_form β
  exact ⟨A, ε, hε, hA, (u43ModelK.eq_T hind).symm⟩

theorem cfgM1aK_parts {k : ℕ} (h : cfgM1aK k = true) :
    Cover.commOK (pk (wM1a.getD k (0, false)).1 (wM1a.getD k (0, false)).2)
        (clsT 1 (clsR 1)) = true ∧
      (∀ j < (tM1a.getD k []).length, Cover.commOK (tM1aG k j) (clsT 1 (clsR 1)) = true) ∧
      (cfgM1a.getD k []).length = cond (Nat.beq k 0) 16 32 ∧
      cfgOK (tM1aT k) a6T a6N (!Nat.beq k 0) memCM1a (invL.map LM1a.T) (pk cDi false)
        (pk cDmi false) (cfgM1a.getD k []) = true := by
  unfold cfgM1aK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, fun j hj => List.all_eq_true.1 h2 j (List.mem_range.2 hj),
    Nat.eq_of_beq_eq_true h3, h4⟩

theorem cfgIaK_parts {k : ℕ} (h : cfgIaK k = true) :
    Cover.commOK (pk (wIa.getD k (0, false)).1 (wIa.getD k (0, false)).2)
        (clsT 5 (clsR 5)) = true ∧
      (∀ j < (tIa.getD k []).length, Cover.commOK (tIaG k j) (clsT 5 (clsR 5)) = true) ∧
      (cfgIa.getD k []).length = cond (Nat.beq k 0) 16 32 ∧
      cfgOK (tIaT k) a6T a6N (!Nat.beq k 0) memCIa (invL.map LIa.T) (pk cDi false)
        (pk cDmi false) (cfgIa.getD k []) = true := by
  unfold cfgIaK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, fun j hj => List.all_eq_true.1 h2 j (List.mem_range.2 hj),
    Nat.eq_of_beq_eq_true h3, h4⟩

theorem bindsT_M {k : ℕ} (hk : k < 6) :
    gensOK (tM1a.getD k []) (tM1aG k) = true ∧ Nat.beq (tM1aT k 0) (pidn 820 10) = true := by
  have h := bindsT.1
  rw [Bool.and_eq_true] at h
  have h1 := List.all_eq_true.1 h.1 k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at h1
  exact h1

theorem bindsT_I {k : ℕ} (hk : k < 4) :
    gensOK (tIa.getD k []) (tIaG k) = true ∧ Nat.beq (tIaT k 0) (pidn 820 10) = true := by
  have h := bindsT.1
  rw [Bool.and_eq_true] at h
  have h1 := List.all_eq_true.1 h.2 k (List.mem_range.2 hk)
  rw [Bool.and_eq_true] at h1
  exact h1

theorem a6_parts :
    (∀ j < 2, Cover.commOK (CgM1a.G j) (clsT 1 (clsR 1)) = true ∧
        Cover.commOK (LM1a.G j) (clsT 1 (clsR 1)) = true) ∧
      (∀ j < 2, Cover.commOK (CgIa.G j) (clsT 5 (clsR 5)) = true ∧
        Cover.commOK (LIa.G j) (clsT 5 (clsR 5)) = true) ∧
      normOK CgM1a.G CgM1a.GI LM1a.G LM1a.T nmM1a 360 = true ∧
      normOK CgIa.G CgIa.GI LIa.G LIa.T nmIa 360 = true ∧
      ordP 3 (LM1a.G 0) = true ∧ ordP 5 (LM1a.G 1) = true ∧ ordP 3 (LIa.G 0) = true ∧
      ordP 5 (LIa.G 1) = true ∧
      ∀ j < 360, invL.contains j = true ∨ (invol (LM1a.T j) = false ∧ invol (LIa.T j) = false) := by
  have h := a6
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hall, n1⟩, n2⟩, o1⟩, o2⟩, o3⟩, o4⟩, hinv⟩ := h
  refine ⟨fun j hj => ?_, fun j hj => ?_, n1, n2, o1, o2, o3, o4, fun j hj => ?_⟩
  · have h1 := List.all_eq_true.1 hall j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true] at h1
    exact ⟨h1.1.1.1, h1.1.1.2⟩
  · have h1 := List.all_eq_true.1 hall j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true] at h1
    exact ⟨h1.1.2, h1.2⟩
  · have h1 := List.all_eq_true.1 hinv j (List.mem_range.2 hj)
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h1
    exact h1

structure A6Data (c : ℕ) (L C : Subgroup (Equiv.Perm (Fin 820))) (LT CT : ℕ → ℕ) : Prop where
  hle : L ≤ psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))
  hnorm : psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))) ≤
    normalizer (L : Set (Equiv.Perm (Fin 820)))
  hcard : Nat.card L = 360
  hpow : ∃ a, L.relIndex (psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))) = 2 ^ a
  hodd : L ≤ CFSG.ComponentClassification.HarrisLit.Q81.oddPart
    (psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820))))
  hiso : Nonempty (↥L ≃* alternatingGroup (Fin 6))
  hCeq : C = psi.range ⊓ centralizer ({tRep c} : Set (Equiv.Perm (Fin 820)))
  hLall : ∀ y ∈ L, ∃ i < 360, PRep 820 10 (LT i) y
  hCpts : ∀ i < 720, ∃ y ∈ C, PRep 820 10 (CT i) y

theorem a6data_M1a : A6Data 1 (closure (gK (lM1a.map (·, false)) '' {k | k < 2}))
    (closure (gK cgM1a '' {k | k < 2})) LM1a.T CgM1a.T := by
  obtain ⟨-, -, -, g4, g5, -, -, -, -, -, z4, z5, -, -, -, -, -, n4, n5, -, -, -, -, -, e4, e5, -, -⟩ :=
    bindsS_cen
  obtain ⟨hcm, -, hnm, -, o1, o2, -⟩ := a6_parts
  obtain ⟨hCeq, hKle, hnorm, hKcard, -, hall, hpts⟩ := pair_facts (c := 1) (lC := cgM1a)
    (lK := lM1a.map (·, false)) (by norm_num) g4 g5 (by decide) (by decide) (by rw [e4]; rfl)
    (by rw [e5]; rfl) e4 e5 CgM1a.cl CgM1a.tr (by decide) z4 baseL_lt CgM1a.k LM1a.cl LM1a.tr
    (by decide) z5 baseL_lt LM1a.k CgM1a.h hcm hnm (by rw [card_cen1, n4])
    (by rw [n4]; norm_num) (by rw [n5]; norm_num)
  rw [n5] at hKcard hall
  rw [n4] at hpts
  have hd' : ∀ x ∈ lM1a.map (·, false), detOf x.1 ≠ 0 := by decide
  obtain ⟨hD, n6, -, -, g6, -, -⟩ := bindsD
  simp only [Bool.and_eq_true] at hD
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨d0, d1⟩, -⟩, -⟩, -⟩, -⟩, z6⟩, -⟩, -⟩ := hD
  obtain ⟨hpow, hodd, hiso⟩ := a6_core (c := 1) (codes := lM1a) (GK := LM1a.G) hKle hKcard
    card_cen1 (fun j hj => prep_gensOK g5 hd' j (lt_of_lt_of_eq hj rfl)) o1 o2
    (fun k hk => by interval_cases k <;> rfl) (by decide)
    (fun k hk => by interval_cases k; exacts [d0, d1]) g6 DgM1a.cl DgM1a.tr (by decide) n6 z6
    DgM1a.k
  exact ⟨hKle, hnorm, hKcard, hpow, hodd, hiso, hCeq, hall, hpts⟩

theorem a6data_Ia : A6Data 5 (closure (gK (lIa.map (·, false)) '' {k | k < 2}))
    (closure (gK cgIa '' {k | k < 2})) LIa.T CgIa.T := by
  obtain ⟨-, -, -, -, -, g6, g7, -, -, -, -, -, z6, z7, -, -, -, -, -, n6, n7, -, -, -, -, -, e6, e7⟩ :=
    bindsS_cen
  obtain ⟨-, hcm, -, hnm, -, -, o3, o4, -⟩ := a6_parts
  obtain ⟨hCeq, hKle, hnorm, hKcard, -, hall, hpts⟩ := pair_facts (c := 5) (lC := cgIa)
    (lK := lIa.map (·, false)) (by norm_num) g6 g7 (by decide) (by decide) (by rw [e6]; rfl)
    (by rw [e7]; rfl) e6 e7 CgIa.cl CgIa.tr (by decide) z6 baseL_lt CgIa.k LIa.cl LIa.tr
    (by decide) z7 baseL_lt LIa.k CgIa.h hcm hnm (by rw [card_cen5, n6])
    (by rw [n6]; norm_num) (by rw [n7]; norm_num)
  rw [n7] at hKcard hall
  rw [n6] at hpts
  have hd' : ∀ x ∈ lIa.map (·, false), detOf x.1 ≠ 0 := by decide
  obtain ⟨hD, -, nD, -, -, gD, -⟩ := bindsD
  simp only [Bool.and_eq_true] at hD
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, d2⟩, d3⟩, -⟩, -⟩, -⟩, zD⟩, -⟩ := hD
  obtain ⟨hpow, hodd, hiso⟩ := a6_core (c := 5) (codes := lIa) (GK := LIa.G) hKle hKcard
    card_cen5 (fun j hj => prep_gensOK g7 hd' j (lt_of_lt_of_eq hj rfl)) o3 o4
    (fun k hk => by interval_cases k <;> rfl) (by decide)
    (fun k hk => by interval_cases k; exacts [d2, d3]) gD DgIa.cl DgIa.tr (by decide) nD zD
    DgIa.k
  exact ⟨hKle, hnorm, hKcard, hpow, hodd, hiso, hCeq, hall, hpts⟩

theorem a6_points :
    ∀ c' < 2, ∀ j < a6N c', ∀ σ, PRep 820 10 (a6T c' j) σ → A6Normal psi.range σ := by
  have D1 := a6data_M1a
  have D5 := a6data_Ia
  intro c' hc' j hj σ hσ
  interval_cases c'
  · obtain ⟨h, hh, e⟩ := eq_conj_of_cls (c := 1) (by norm_num) hj hσ
    rw [e]
    exact a6Normal_conj (le_normalizer hh) (a6Normal_of_le D1.hle D1.hnorm D1.hiso)
  · obtain ⟨h, hh, e⟩ := eq_conj_of_cls (c := 5) (by norm_num) hj hσ
    rw [e]
    exact a6Normal_conj (le_normalizer hh) (a6Normal_of_le D5.hle D5.hnorm D5.hiso)

theorem hLs_of {c : ℕ} {L C : Subgroup (Equiv.Perm (Fin 820))} {LT CT : ℕ → ℕ}
    (D : A6Data c L C LT CT)
    (hinv : ∀ j < 360, invL.contains j = true ∨ invol (LT j) = false) :
    ∀ y ∈ L, orderOf y = 2 → ∃ p ∈ invL.map LT, PRep 820 10 p y := by
  intro y hy hy2
  obtain ⟨i, hi, hp⟩ := D.hLall y hy
  have hv := (invol_iff hp).2 (mul_self_of_orderOf hy2)
  rcases hinv i hi with h | h
  · exact ⟨LT i, List.mem_map_of_mem (List.contains_iff_mem.1 h), hp⟩
  · rw [hv] at h
    exact Bool.noConfusion h

theorem hmem_of {c : ℕ} {L C : Subgroup (Equiv.Perm (Fin 820))} {LT CT : ℕ → ℕ}
    (D : A6Data c L C LT CT) {T : ℕ → ℕ} {N : ℕ} :
    ∀ i < N, ((List.range 720).any fun j => Nat.beq (CT j) (T i)) = true →
      ∀ σ, PRep 820 10 (T i) σ → σ ∈ psi.range := by
  intro i _ hm σ hp
  obtain ⟨j, hj, hb⟩ := List.any_eq_true.1 hm
  have e := Nat.eq_of_beq_eq_true hb
  obtain ⟨y, hy, hpy⟩ := D.hCpts j (List.mem_range.1 hj)
  rw [e] at hpy
  rw [prep_eq hp hpy]
  rw [D.hCeq] at hy
  exact (mem_inf.mp hy).1

theorem cfg_M1a {v : Equiv.Perm (Fin 820)} (hv2 : orderOf v = 2)
    (hvt : v * tRep 1 = tRep 1 * v) {A : GL (Fin 4) F9} {ε : ℕ} (hε : ε ≤ 1)
    (hA : IsUnitaryF A) (hv : v = perm820 A * frob820 ^ ε)
    (hl : ∃ y ∈ closure (gK (lM1a.map (·, false)) '' {k | k < 2}), orderOf y = 2 ∧
      orderOf (v * y) = 8) : A6Normal psi.range v := by
  have D := a6data_M1a
  have hLeq := oddPart_eq_of_le D.hle D.hnorm D.hpow D.hodd
  have hLs := hLs_of D (fun j hj => (a6_parts.2.2.2.2.2.2.2.2 j hj).imp_right And.left)
  have hlo := cfgM1a_lo
  have hhi := cfgM1a_hi
  simp only [Bool.and_eq_true] at hlo hhi
  obtain ⟨⟨k0, k1⟩, k2⟩ := hlo
  obtain ⟨⟨k3, k4⟩, k5⟩ := hhi
  have p0 := cfgM1aK_parts k0
  have p1 := cfgM1aK_parts k1
  have p2 := cfgM1aK_parts k2
  have p3 := cfgM1aK_parts k3
  have p4 := cfgM1aK_parts k4
  have p5 := cfgM1aK_parts k5
  obtain ⟨-, nT0, nT1, nT2, nT3, nT4, nT5, -, -, -, -, gT0, gT1, gT2, gT3, gT4, gT5, -⟩ := bindsT
  obtain ⟨hFF, hFA, -⟩ := run_F
  obtain ⟨hII, hIA, -⟩ := run_I
  obtain ⟨hUU4, hUA4⟩ := conj_outer hFF hFA
  obtain ⟨hUU5, hUA5⟩ := conj_outer hII hIA
  rw [d_facts.2.1] at hUU4 hUA4
  rw [d_facts.2.2] at hUU5 hUA5
  have hsq := (mul_self_of_orderOf hv2).1
  rw [hv] at hsq
  rcases coset_cases hε hA hsq with h | h | h | h | h | h <;> rw [← hv] at h
  · have hwA : eK (wM1a.getD 0 (0, false)).1 (wM1a.getD 0 (0, false)).2 ∈ psi.range :=
      eK_mem_range (k := (wM1a.getD 0 (0, false)).1) (by decide)
    exact cfg_coset (c := 1) (by norm_num) hLeq card_cen1 (spec_of (d := 3) (by decide)
      (by norm_num)) p0.1 (Or.inl ⟨hwA, nT0⟩) (bindsT_M (by norm_num)).1 (by decide)
      (G := tM1aG 0) (T := tM1aT 0) (by rw [gT0]; rfl) TM0.cl TM0.tr (by decide) (bindsT_M (by norm_num)).2 TM0.k p0.2.1
      p0.2.2.2 (p0.2.2.1.trans (by rw [nT0]; rfl)) (fun h => absurd h (by decide)) (hmem_of D)
      hLs a6_points v hv2 hvt (mul_mem h (inv_mem hwA)) hl
  · have hcos : eK (wM1a.getD 1 (0, false)).1 (wM1a.getD 1 (0, false)).2 * uM1⁻¹ ∈ psi.range :=
      eK_coset (spec_of (d := 6) (by decide) (by norm_num)) spec_cM1 _
    have hwA := not_mem_of_coset hcos run_M1.2.1
    have hww := sq_mem_of_coset (eK_mem_normalizer' spec_cM1 false) run_M1.1 hcos
    exact cfg_coset (c := 1) (by norm_num) hLeq card_cen1 (spec_of (d := 6) (by decide)
      (by norm_num)) p1.1 (Or.inr ⟨hwA, hww, nT1⟩) (bindsT_M (by norm_num)).1 (by decide)
      (G := tM1aG 1) (T := tM1aT 1) (by rw [gT1]; rfl) TM1.cl TM1.tr (by decide) (bindsT_M (by norm_num)).2 TM1.k p1.2.1
      p1.2.2.2 (p1.2.2.1.trans (by rw [nT1]; rfl)) (fun _ => hwA) (hmem_of D)
      hLs a6_points v hv2 hvt (coset_trans h hcos) hl
  · have hcos : eK (wM1a.getD 2 (0, false)).1 (wM1a.getD 2 (0, false)).2 * uF⁻¹ ∈ psi.range :=
      eK_coset (spec_of (d := 3) (by decide) (by norm_num)) cI_spec _
    have hwA := not_mem_of_coset hcos hFA
    have hww := sq_mem_of_coset (eK_mem_normalizer' cI_spec true) hFF hcos
    exact cfg_coset (c := 1) (by norm_num) hLeq card_cen1 (spec_of (d := 3) (by decide)
      (by norm_num)) p2.1 (Or.inr ⟨hwA, hww, nT2⟩) (bindsT_M (by norm_num)).1 (by decide)
      (G := tM1aG 2) (T := tM1aT 2) (by rw [gT2]; rfl) TM2.cl TM2.tr (by decide) (bindsT_M (by norm_num)).2 TM2.k p2.2.1
      p2.2.2.2 (p2.2.2.1.trans (by rw [nT2]; rfl)) (fun _ => hwA) (hmem_of D)
      hLs a6_points v hv2 hvt (coset_trans h hcos) hl
  · have hcos : eK (wM1a.getD 3 (0, false)).1 (wM1a.getD 3 (0, false)).2 * uI⁻¹ ∈ psi.range :=
      eK_coset (spec_of (d := 1) (by decide) (by norm_num)) spec_cDi _
    have hwA := not_mem_of_coset hcos hIA
    have hww := sq_mem_of_coset (eK_mem_normalizer' spec_cDi true) hII hcos
    exact cfg_coset (c := 1) (by norm_num) hLeq card_cen1 (spec_of (d := 1) (by decide)
      (by norm_num)) p3.1 (Or.inr ⟨hwA, hww, nT3⟩) (bindsT_M (by norm_num)).1 (by decide)
      (G := tM1aG 3) (T := tM1aT 3) (by rw [gT3]; rfl) TM3.cl TM3.tr (by decide) (bindsT_M (by norm_num)).2 TM3.k p3.2.1
      p3.2.2.2 (p3.2.2.1.trans (by rw [nT3]; rfl)) (fun _ => hwA) (hmem_of D)
      hLs a6_points v hv2 hvt (coset_trans h hcos) hl
  · have hcos : eK (wM1a.getD 4 (0, false)).1 (wM1a.getD 4 (0, false)).2 * (eK cM1 true)⁻¹ ∈
        psi.range := eK_coset (spec_of (d := 6) (by decide) (by norm_num)) spec_cM1 _
    have hwA := not_mem_of_coset hcos hUA4
    have hww := sq_mem_of_coset (eK_mem_normalizer' spec_cM1 true) hUU4 hcos
    exact cfg_coset (c := 1) (by norm_num) hLeq card_cen1 (spec_of (d := 6) (by decide)
      (by norm_num)) p4.1 (Or.inr ⟨hwA, hww, nT4⟩) (bindsT_M (by norm_num)).1 (by decide)
      (G := tM1aG 4) (T := tM1aT 4) (by rw [gT4]; rfl) TM4.cl TM4.tr (by decide) (bindsT_M (by norm_num)).2 TM4.k p4.2.1
      p4.2.2.2 (p4.2.2.1.trans (by rw [nT4]; rfl)) (fun _ => hwA) (hmem_of D)
      hLs a6_points v hv2 hvt (coset_trans h hcos) hl
  · have hcos : eK (wM1a.getD 5 (0, false)).1 (wM1a.getD 5 (0, false)).2 * (eK cDmi true)⁻¹ ∈
        psi.range := eK_coset (spec_of (d := 2) (by decide) (by norm_num)) spec_cDmi _
    have hwA := not_mem_of_coset hcos hUA5
    have hww := sq_mem_of_coset (eK_mem_normalizer' spec_cDmi true) hUU5 hcos
    exact cfg_coset (c := 1) (by norm_num) hLeq card_cen1 (spec_of (d := 2) (by decide)
      (by norm_num)) p5.1 (Or.inr ⟨hwA, hww, nT5⟩) (bindsT_M (by norm_num)).1 (by decide)
      (G := tM1aG 5) (T := tM1aT 5) (by rw [gT5]; rfl) TM5.cl TM5.tr (by decide) (bindsT_M (by norm_num)).2 TM5.k p5.2.1
      p5.2.2.2 (p5.2.2.1.trans (by rw [nT5]; rfl)) (fun _ => hwA) (hmem_of D)
      hLs a6_points v hv2 hvt (coset_trans h hcos) hl

theorem cfg_Ia {v : Equiv.Perm (Fin 820)} (hv2 : orderOf v = 2)
    (hvt : v * tRep 5 = tRep 5 * v) {A : GL (Fin 4) F9} {ε : ℕ} (hε : ε ≤ 1)
    (hA : IsUnitaryF A) (hv : v = perm820 A * frob820 ^ ε)
    (hl : ∃ y ∈ closure (gK (lIa.map (·, false)) '' {k | k < 2}), orderOf y = 2 ∧
      orderOf (v * y) = 8) : A6Normal psi.range v := by
  have D := a6data_Ia
  have hLeq := oddPart_eq_of_le D.hle D.hnorm D.hpow D.hodd
  have hLs := hLs_of D (fun j hj => (a6_parts.2.2.2.2.2.2.2.2 j hj).imp_right And.right)
  have hc := cfgIa_all
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, hn1⟩, hn2⟩ := hc
  have p0 := cfgIaK_parts k0
  have p1 := cfgIaK_parts k1
  have p2 := cfgIaK_parts k2
  have p3 := cfgIaK_parts k3
  obtain ⟨-, -, -, -, -, -, -, nI0, nI1, nI2, nI3, -, -, -, -, -, -, gI0, gI1, gI2, gI3⟩ := bindsT
  obtain ⟨hII, hIA, -⟩ := run_I
  obtain ⟨hUU5, hUA5⟩ := conj_outer hII hIA
  rw [d_facts.2.2] at hUU5 hUA5
  have hsq := (mul_self_of_orderOf hv2).1
  rw [hv] at hsq
  rcases coset_cases hε hA hsq with h | h | h | h | h | h <;> rw [← hv] at h
  · have hwA : eK (wIa.getD 0 (0, false)).1 (wIa.getD 0 (0, false)).2 ∈ psi.range :=
      eK_mem_range (k := (wIa.getD 0 (0, false)).1) (by decide)
    exact cfg_coset (c := 5) (by norm_num) hLeq card_cen5 (spec_of (d := 3) (by decide)
      (by norm_num)) p0.1 (Or.inl ⟨hwA, nI0⟩) (bindsT_I (by norm_num)).1 (by decide)
      (G := tIaG 0) (T := tIaT 0) (by rw [gI0]; rfl) TI0.cl TI0.tr (by decide) (bindsT_I (by norm_num)).2 TI0.k p0.2.1
      p0.2.2.2 (p0.2.2.1.trans (by rw [nI0]; rfl)) (fun h => absurd h (by decide)) (hmem_of D)
      hLs a6_points v hv2 hvt (mul_mem h (inv_mem hwA)) hl
  · have hcos : eK (wIa.getD 1 (0, false)).1 (wIa.getD 1 (0, false)).2 * uM1⁻¹ ∈ psi.range :=
      eK_coset (spec_of (d := 6) (by decide) (by norm_num)) spec_cM1 _
    have hwA := not_mem_of_coset hcos run_M1.2.1
    have hww := sq_mem_of_coset (eK_mem_normalizer' spec_cM1 false) run_M1.1 hcos
    exact cfg_coset (c := 5) (by norm_num) hLeq card_cen5 (spec_of (d := 6) (by decide)
      (by norm_num)) p1.1 (Or.inr ⟨hwA, hww, nI1⟩) (bindsT_I (by norm_num)).1 (by decide)
      (G := tIaG 1) (T := tIaT 1) (by rw [gI1]; rfl) TI1.cl TI1.tr (by decide) (bindsT_I (by norm_num)).2 TI1.k p1.2.1
      p1.2.2.2 (p1.2.2.1.trans (by rw [nI1]; rfl)) (fun _ => hwA) (hmem_of D)
      hLs a6_points v hv2 hvt (coset_trans h hcos) hl
  · exact (none_of_noneIa (prep_pk' cI_spec true) hn1 hvt h).elim
  · have hcos : eK (wIa.getD 2 (0, false)).1 (wIa.getD 2 (0, false)).2 * uI⁻¹ ∈ psi.range :=
      eK_coset (spec_of (d := 1) (by decide) (by norm_num)) spec_cDi _
    have hwA := not_mem_of_coset hcos hIA
    have hww := sq_mem_of_coset (eK_mem_normalizer' spec_cDi true) hII hcos
    exact cfg_coset (c := 5) (by norm_num) hLeq card_cen5 (spec_of (d := 1) (by decide)
      (by norm_num)) p2.1 (Or.inr ⟨hwA, hww, nI2⟩) (bindsT_I (by norm_num)).1 (by decide)
      (G := tIaG 2) (T := tIaT 2) (by rw [gI2]; rfl) TI2.cl TI2.tr (by decide) (bindsT_I (by norm_num)).2 TI2.k p2.2.1
      p2.2.2.2 (p2.2.2.1.trans (by rw [nI2]; rfl)) (fun _ => hwA) (hmem_of D)
      hLs a6_points v hv2 hvt (coset_trans h hcos) hl
  · exact (none_of_noneIa (prep_pk' spec_cM1 true) hn2 hvt h).elim
  · have hcos : eK (wIa.getD 3 (0, false)).1 (wIa.getD 3 (0, false)).2 * (eK cDmi true)⁻¹ ∈
        psi.range := eK_coset (spec_of (d := 2) (by decide) (by norm_num)) spec_cDmi _
    have hwA := not_mem_of_coset hcos hUA5
    have hww := sq_mem_of_coset (eK_mem_normalizer' spec_cDmi true) hUU5 hcos
    exact cfg_coset (c := 5) (by norm_num) hLeq card_cen5 (spec_of (d := 2) (by decide)
      (by norm_num)) p3.1 (Or.inr ⟨hwA, hww, nI3⟩) (bindsT_I (by norm_num)).1 (by decide)
      (G := tIaG 3) (T := tIaT 3) (by rw [gI3]; rfl) TI3.cl TI3.tr (by decide) (bindsT_I (by norm_num)).2 TI3.k p3.2.1
      p3.2.2.2 (p3.2.2.1.trans (by rw [nI3]; rfl)) (fun _ => hwA) (hmem_of D)
      hLs a6_points v hv2 hvt (coset_trans h hcos) hl

theorem rep_all : ∀ c < 6, RepFacts psi.range u43ModelK.T.range (tRep c) := by
  intro c hc
  interval_cases c
  · exact rep_In _
  · have D := a6data_M1a
    refine RepFacts.a6 _ D.hle D.hnorm D.hcard D.hpow D.hodd D.hiso ?_
    intro v hv hv2 hvt hl
    obtain ⟨A, ε, hε, hA, e⟩ := aut_form hv
    exact cfg_M1a hv2 hvt hε hA e hl
  · exact rep_M1b _
  · exact rep_Fa _
  · exact rep_Fb _
  · have D := a6data_Ia
    refine RepFacts.a6 _ D.hle D.hnorm D.hcard D.hpow D.hodd D.hiso ?_
    intro v hv hv2 hvt hl
    obtain ⟨A, ε, hε, hA, e⟩ := aut_form hv
    exact cfg_Ia hv2 hvt hε hA e hl

theorem p1ModelFacts_u43K : P1ModelFacts X₀ := by
  refine p1ModelFacts_of_facts u43ModelK (A₀ := psi.range) rfl (reps := repsAll) ?_ ?_
  · intro τ hτ h2
    obtain ⟨A, ε, hε, hA, rfl⟩ := aut_form hτ
    exact inv_cover hε hA h2
  · rintro t ⟨c, hc, rfl | rfl⟩
    · exact rep_all c hc
    · exact repFacts_conj dK_mem_normalizer
        (mem_range_T_of_mem_normalizer u43ModelK dK_mem_normalizer) (rep_all c hc)

end CertificateChecks.KernelPermCent.U43P1

end
