module

public import Certificates.Kernel.P1L43.Checks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecC
public import CFSG.Certificates.Kernel.OrbFindSound
public import CFSG.Certificates.Kernel.P1Model.Facts
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

set_option maxRecDepth 400000

@[expose] public section


namespace CertificateChecks.KernelP1L43

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.ArrEnum CFSG.KC.OrbFind
  CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.Certificates Subgroup

@[expose] noncomputable def pp (P : ℕ) : Equiv.Perm (Fin 80) :=
  CFSG.Monster.B.Co2.permOfArr 80 (unpack 80 7 P)

theorem prep_pp {P Q : ℕ} (h : permOK 80 7 (mask 7) (80 * 7) P Q = true) :
    PRep 80 7 P (pp P) :=
  prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr (isInvA_unpack h)).1

theorem hn80 : (80 : ℕ) < 2 ^ 32 := by norm_num

theorem permOfArr_eq {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n t g) : CFSG.Monster.B.Co2.permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => h.lt hi, fun i hi j hj hij => ?_⟩
    rw [h.apply hi, h.apply hj] at hij
    have := g.injective (Fin.ext hij)
    exact congrArg Fin.val this
  rw [CFSG.Monster.B.Co2.permOfArr, dif_pos hc]
  exact Equiv.ext fun x => Fin.ext (h x)

theorem tp_of_bind {T : Table} {P : ℕ} {g : Equiv.Perm (Fin 80)} (hb : bindT T P = true)
    (hP : PRep 80 7 P g) : tp 80 T = g ∧ CFSG.Sporadic.Th.Rep 80 T g := by
  have h1 : CFSG.Monster.B.Co2.Rep 80 (natArr T) g := by
    rw [arrBind_sound hb]
    exact rep_unpack hP
  exact ⟨permOfArr_eq h1, co2Rep_natArr_iff.1 h1⟩

theorem prep_of_bind {T : Table} {P : ℕ} {g : Equiv.Perm (Fin 80)} (hb : bindT T P = true)
    (hT : CFSG.Sporadic.Th.Rep 80 T g) : PRep 80 7 P g := by
  apply prep_of_rep
  rw [← arrBind_sound hb]
  exact co2Rep_natArr_iff.2 hT

theorem pp_mul_self {P : ℕ} (h : selfInv P = true) : pp P * pp P = 1 := by
  have h' : permOK 80 7 (mask 7) (80 * 7) P P = true := h
  have h1 := prep_pp h'
  have h2 := prep_eq (prep_inv h1 h') h1
  have h3 := inv_mul_cancel (pp P)
  rwa [h2] at h3

theorem inv_eq_of_mul_self {g : Equiv.Perm (Fin 80)} (h : g * g = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right h

theorem binds22240 : Binds 80 7 CertificateChecks.KernelSchreierFam.L43.S 11 6
    CertificateChecks.KernelSchreierFam.L43.BP chainS baseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel,
    fun j hj => arrBind_sound (CertificateChecks.KernelSchreierFam.L43.bS j hj), by decide +kernel,
    CertificateChecks.KernelSchreierFam.L43.bget⟩

theorem mem_of_sP {P : ℕ} {g : Equiv.Perm (Fin 80)} (hP : PRep 80 7 P g) (h : sP P = true) :
    g ∈ pi.range := by
  unfold sP at h
  rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hs := siftK_soundR binds22240 CertificateChecks.KernelSchreierFam.L43.perm
    CertificateChecks.KernelSchreierFam.L43.hl rfl (Nat.eq_of_beq_eq_true h1) h2 h3
  rw [range_pi, ← chainQ_eq]
  exact (siftA_iff_mem_originalSubgroup chainArrays_l43 (by norm_num) chain_check
    (rep_unpack hP)).1 hs

theorem comm_of_cm {P Q : ℕ} {g h : Equiv.Perm (Fin 80)} (hP : PRep 80 7 P g)
    (hQ : PRep 80 7 Q h) (hc : cm P Q = true) : g * h = h * g := by
  unfold cm eq22 at hc
  rw [CFSG.KS.Raw.Orb.allN_iff] at hc
  refine Equiv.ext fun x => Fin.ext ?_
  have := Nat.eq_of_beq_eq_true (hc x x.2)
  rw [hQ x, hP (h x), hP x, hQ (g x)] at this
  exact this

theorem card_range : Nat.card pi.range = 6065280 := by
  rw [range_pi, card_closure_pi]

theorem closure_gens : closure (l43Gens '' {k | k < 2}) = pi.range := by
  have e : pgTbls.size = 2 := rfl
  have h := l43_groupData.gen
  rw [e] at h
  exact h.symm

theorem prep_gens {G : ℕ → ℕ} (h0 : bindT (tm codeA) (G 0) = true)
    (h1 : bindT (tm codeB) (G 1) = true) : ∀ k < 2, PRep 80 7 (G k) (l43Gens k) := by
  intro k hk
  interval_cases k
  · exact prep_of_bind h0 (l43_groupData.rep 0 (by decide))
  · exact prep_of_bind h1 (l43_groupData.rep 1 (by decide))

theorem ps_lt : ∀ p ∈ ps, p < 80 := by decide

theorem gens2106 : ∀ k < 2, PRep 80 7 (K2106.G k) (l43Gens k) :=
  prep_gens binds.2.2.2.1 binds.2.2.2.2.1

theorem conj_closed {X : Type*} [Group X] [Finite X] {s O : Set X}
    (hs : ∀ g ∈ s, ∀ x ∈ O, g * x * g⁻¹ ∈ O) : ∀ g ∈ closure s, ∀ x ∈ O, g * x * g⁻¹ ∈ O := by
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one =>
    intro y hy
    rw [one_mul, inv_one, mul_one]
    exact hy
  | mul a b _ _ ha hb =>
    intro y hy
    have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha _ (hb y hy)
  | inv a _ ha =>
    intro y hy
    obtain ⟨z, hz, e⟩ := surj_of_mapsTo (fun z => a * z * a⁻¹)
      (fun u v e => by simpa using e) ha y hy
    have e2 : a⁻¹ * y * a⁻¹⁻¹ = z := by
      rw [← e]
      group
    rw [e2]
    exact hz

theorem class_facts {N r : ℕ} {G GI T E D S : ℕ → ℕ} {t : Equiv.Perm (Fin 80)}
    (hh : headK 80 7 2 G GI = true) (hg : ∀ k < 2, PRep 80 7 (G k) (l43Gens k))
    (hcl : ∀ i < N, closPt 80 7 2 N G GI T E i = true)
    (htr : ∀ i < N, treePt 2 N r E D i = true) (hr : r < N) (ht : PRep 80 7 (T r) t)
    (hK : distinctK N (fun i => pkeyK 80 7 ps (T i)) S = true) :
    (conjClass pi.range t).ncard = N ∧
      N * Nat.card ↥(pi.range ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 80)))) = 6065280 ∧
      ∀ i < N, ∀ v, PRep 80 7 (T i) v → ∃ g ∈ pi.range, v = g * t * g⁻¹ := by
  obtain ⟨c, hc, hreach, hcl', hinj⟩ := conjOrb_reps (g := l43Gens) (t := t) hn80 hh hg hcl htr
    hr ht ps_lt hK
  rw [closure_gens] at hreach
  have hcr : c r = t := prep_eq (hc r hr) ht
  have hset : conjClass pi.range t = {y | ∃ i < N, c i = (MonoidHom.id _) y} := by
    ext x
    constructor
    · rintro ⟨g, hg', rfl⟩
      rw [← closure_gens] at hg'
      refine conj_closed (O := {y | ∃ i < N, c i = (MonoidHom.id _) y}) ?_ g hg' t
        ⟨r, hr, hcr⟩
      rintro _ ⟨k, hk, rfl⟩ _ ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hcl' i hi k hk
      exact ⟨j, hj, e.symm⟩
    · rintro ⟨i, hi, e⟩
      obtain ⟨h, hh', e2⟩ := hreach i hi
      exact ⟨h, hh', by rw [← e2]; exact e.symm⟩
  have hN := ncard_of_reps (MonoidHom.id _) (fun _ _ h => h) c (fun i _ => ⟨c i, rfl⟩) hinj
  rw [← hset] at hN
  have hmul := ncard_conjClass_mul_card pi.range t
  rw [hN, card_range] at hmul
  refine ⟨hN, hmul, fun i hi v hv => ?_⟩
  obtain ⟨h, hh', e2⟩ := hreach i hi
  exact ⟨h, hh', by rw [prep_eq hv (hc i hi), e2]⟩

theorem group_facts {N ng : ℕ} {G GI T E D S : ℕ → ℕ}
    (hh : headK 80 7 ng G GI = true)
    (hcl : ∀ i < N, closPtL 80 7 ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn 80 7)
    (hK : distinctK N (fun i => pkeyK 80 7 ps (T i)) S = true) :
    Nat.card (closure ((fun k => pp (G k)) '' {k | k < ng})) = N ∧
      ∀ y ∈ closure ((fun k => pp (G k)) '' {k | k < ng}), ∃ i < N, PRep 80 7 (T i) y := by
  have hg : ∀ k < ng, PRep 80 7 (G k) (pp (G k)) :=
    fun k hk => prep_pp ((headK_spec hh).2 k hk).2.2
  have hid : PRep 80 7 (T 0) 1 := by
    rw [h0]
    exact prep_pidn (by norm_num) (by norm_num)
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ := leftOrb_reps (g := fun k => pp (G k)) hn80 hg hcl htr
    hN hid ps_lt hK
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) (fun _ _ h => h) (fun k => pp (G k)) c
    ⟨0, hN, hc0⟩ hmem hcl' hinj
  refine ⟨hcard, fun y hy => ?_⟩
  obtain ⟨i, hi, e⟩ := hall y hy
  have e' : c i = y := e
  exact ⟨i, hi, by rw [← e']; exact hc i hi⟩

theorem rowFacts_of {r : ClassRow} {t : Equiv.Perm (Fin 80)} {G : ℕ → ℕ} {T0 T1 : Table}
    (hrep : CFSG.Sporadic.Th.Rep 80 r.rep t) (htp : tp 80 r.rep = t)
    (hord : orderOf t = 2) (hout : r.outer = true ↔ t ∉ pi.range)
    (hgens : r.centGens = [T0, T1]) (h0 : tp 80 T0 = pp (G 0)) (h1 : tp 80 T1 = pp (G 1))
    (hle : ∀ k < 2, pp (G k) ∈ pi.range ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 80))))
    (hcard : Nat.card (closure ((fun k => pp (G k)) '' {k | k < 2})) = r.centOrder)
    (hcls : (conjClass pi.range t).ncard = r.classSize)
    (hmul : r.classSize *
      Nat.card ↥(pi.range ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 80)))) = 6065280)
    (hprod : r.classSize * r.centOrder = 6065280) : RowFacts pi.range r := by
  subst htp
  have himg : tp 80 '' {x | x ∈ r.centGens.toArray} = (fun k => pp (G k)) '' {k | k < 2} := by
    rw [hgens]
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨x, (rfl | rfl), rfl⟩
      · exact ⟨0, by norm_num, h0.symm⟩
      · exact ⟨1, by norm_num, h1.symm⟩
    · rintro ⟨k, hk, rfl⟩
      interval_cases k
      · exact ⟨T0, Or.inl rfl, h0⟩
      · exact ⟨T1, Or.inr rfl, h1⟩
  have hC : Nat.card ↥(pi.range ⊓ centralizer ({tp 80 r.rep} : Set (Equiv.Perm (Fin 80)))) =
      r.centOrder := by
    have hpos : 0 < r.classSize := by
      rcases Nat.eq_zero_or_pos r.classSize with h | h
      · rw [h] at hprod
        omega
      · exact h
    exact Nat.eq_of_mul_eq_mul_left hpos (hmul.trans hprod.symm)
  have hcent : closure (tp 80 '' {x | x ∈ r.centGens.toArray}) =
      pi.range ⊓ centralizer ({tp 80 r.rep} : Set (Equiv.Perm (Fin 80))) := by
    rw [himg]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact hle k hk
    · rw [hC, hcard]
  exact ⟨hrep, hord, hout, hcent, hC, hcls⟩

theorem prep_si {P : ℕ} (h : selfInv P = true) : PRep 80 7 P (pp P) := prep_pp h

theorem row_of_check {r : ClassRow} {P : ℕ} {Uo : Option ℕ} {G GI TT E D S : ℕ → ℕ}
    {T0 T1 : Table} (hsi : selfInv P = true) (hb : bindT r.rep P = true)
    (hrow : rowK P Uo G 2 = true)
    (hUo : ∀ u, Uo = some u → ∃ σ, PRep 80 7 u σ ∧ σ ∉ pi.range)
    (houter : r.outer = Uo.isSome)
    (hgens : r.centGens = [T0, T1]) (hb0 : bindT T0 (G 0) = true) (hb1 : bindT T1 (G 1) = true)
    (hh : headK 80 7 2 G GI = true)
    (hcl : ∀ i < r.centOrder, closPtL 80 7 2 r.centOrder G TT E i = true)
    (htr : ∀ i < r.centOrder, treePt 2 r.centOrder 0 E D i = true) (h0 : TT 0 = pidn 80 7)
    (hK : distinctK r.centOrder (fun i => pkeyK 80 7 ps (TT i)) S = true)
    (hcf : (conjClass pi.range (pp P)).ncard = r.classSize ∧ r.classSize *
      Nat.card ↥(pi.range ⊓ centralizer ({pp P} : Set (Equiv.Perm (Fin 80)))) = 6065280)
    (hprod : r.classSize * r.centOrder = 6065280) : RowFacts pi.range r := by
  have hP := prep_si hsi
  obtain ⟨htp, hrep⟩ := tp_of_bind hb hP
  unfold rowK at hrow
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hrow
  obtain ⟨hinv, hmem, hgen⟩ := hrow
  rw [CFSG.KS.Raw.Orb.allN_iff] at hgen
  have hG : ∀ k < 2, PRep 80 7 (G k) (pp (G k)) :=
    fun k hk => prep_pp ((headK_spec hh).2 k hk).2.2
  have hpos : 0 < r.centOrder := by
    rcases Nat.eq_zero_or_pos r.centOrder with h | h
    · rw [h] at hprod
      omega
    · exact h
  refine rowFacts_of hrep htp ((isInvK_iff hn80 hP).1 hinv) ?_ hgens
    (tp_of_bind hb0 (hG 0 (by norm_num))).1 (tp_of_bind hb1 (hG 1 (by norm_num))).1 ?_
    (group_facts hh hcl htr hpos h0 hK).1 hcf.1 hcf.2 hprod
  · rw [houter]
    cases Uo with
    | none =>
      have hin := mem_of_sP hP hmem
      exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd hin h⟩
    | some u =>
      obtain ⟨σ, hσ, hσA⟩ := hUo u rfl
      change sP (pc P u) = true at hmem
      have hin := mem_of_sP (prep_pcomp hn80 hP hσ) hmem
      refine ⟨fun _ hPA => hσA ?_, fun _ => rfl⟩
      have e : σ = (pp P)⁻¹ * (pp P * σ) := by group
      rw [e]
      exact mul_mem (inv_mem hPA) hin
  · intro k hk
    have h2 := hgen k hk
    rw [Bool.and_eq_true] at h2
    exact mem_inf.2 ⟨mem_of_sP (hG k hk) h2.1,
      mem_centralizer_singleton_iff.2 (comm_of_cm (hG k hk) hP h2.2)⟩

theorem fac_two : (2 * 6065280 : ℕ).factorization 2 = 8 := by
  rw [show (2 * 6065280 : ℕ) = 2 ^ 8 * 47385 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem runFacts_of {R : Run} {U sng : ℕ} {SG SGI : ℕ → ℕ}
    (hbU : bindT R.u U = true) (hsU : selfInv U = true)
    (hinv : invOK 80 R.u (invT 80 R.u) = true)
    (hb0 : bindT (tm codeA) (K2106.G 0) = true) (hb1 : bindT (tm codeB) (K2106.G 1) = true)
    (hrun : runK U SG sng = true) (hSh : headK 80 7 sng SG SGI = true)
    (hScard : Nat.card (closure ((fun k => pp (SG k)) '' {k | k < sng})) = 256)
    (hrow : pp U ∉ pi.range → ∀ r ∈ R.rows, RowFacts pi.range r.row)
    (htest : ∀ s ∈ closure ((fun k => pp (SG k)) '' {k | k < sng}), orderOf s = 2 →
      ∃ r ∈ R.rows, ∃ g ∈ pi.range, s = g * tp 80 r.row.rep * g⁻¹)
    (hUcl : ∀ r ∈ R.rows, ∃ r' ∈ R.rows, ∃ g ∈ pi.range,
      tp 80 R.u * tp 80 r.row.rep * (tp 80 R.u)⁻¹ = g * tp 80 r'.row.rep * g⁻¹) :
    RunFacts pi.range R := by
  have hU : PRep 80 7 U (pp U) := prep_pp hsU
  obtain ⟨htpU, hrepU⟩ := tp_of_bind hbU hU
  have hUU : tp 80 R.u * tp 80 R.u = 1 := by rw [htpU]; exact pp_mul_self hsU
  have hUi : (tp 80 R.u)⁻¹ = tp 80 R.u := inv_eq_of_mul_self hUU
  have hu2 : tp 80 R.u ^ 2 = 1 := by rw [sq, hUU]
  rw [← htpU] at hU
  unfold runK at hrun
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hrun
  obtain ⟨-, hn0, hn1, hsyl⟩ := hrun
  rw [CFSG.KS.Raw.Orb.allN_iff] at hsyl
  have hg := prep_gens hb0 hb1
  have hnorm : ∀ p ∈ pi.range, tp 80 R.u * p * (tp 80 R.u)⁻¹ ∈ pi.range := by
    intro p hp
    rw [← closure_gens] at hp
    have hle : closure (l43Gens '' {k | k < 2}) ≤
        pi.range.comap (MulAut.conj (tp 80 R.u)).toMonoidHom := by
      rw [closure_le]
      rintro _ ⟨k, hk, rfl⟩
      change tp 80 R.u * l43Gens k * (tp 80 R.u)⁻¹ ∈ pi.range
      rw [hUi]
      have hk' : k < 2 := hk
      have hp' := prep_pcomp hn80 hU (prep_pcomp hn80 (hg k hk') hU)
      rw [← mul_assoc] at hp'
      interval_cases k
      · exact mem_of_sP hp' hn0
      · exact mem_of_sP hp' hn1
    exact hle hp
  have hmemR : ∀ x, x ∈ pi.range ⊔ zpowers (tp 80 R.u) ↔ x ∈ pi.range ∨ x * tp 80 R.u ∈ pi.range :=
    fun x => mem_sup_zpowers_iff hu2 hnorm
  have hSG : ∀ k < sng, PRep 80 7 (SG k) (pp (SG k)) :=
    fun k hk => prep_pp ((headK_spec hSh).2 k hk).2.2
  have hSH : closure ((fun k => pp (SG k)) '' {k | k < sng}) ≤ pi.range ⊔ zpowers (tp 80 R.u) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    change pp (SG k) ∈ pi.range ⊔ zpowers (tp 80 R.u)
    rw [hmemR]
    have hk' := hsyl k hk
    rw [Bool.or_eq_true] at hk'
    rcases hk' with h | h
    · exact Or.inl (mem_of_sP (hSG k hk) h)
    · exact Or.inr (mem_of_sP (prep_pcomp hn80 (hSG k hk) hU) h)
  have hout : tp 80 R.u ∉ pi.range := by
    intro hin
    have hsup : pi.range ⊔ zpowers (tp 80 R.u) = pi.range := sup_eq_left.2 (zpowers_le.2 hin)
    rw [hsup] at hSH
    have := card_dvd_of_le hSH
    rw [hScard, card_range] at this
    norm_num at this
  have hcardR : Nat.card ↥(pi.range ⊔ zpowers (tp 80 R.u)) = 2 * 6065280 := by
    rw [card_sup_zpowers hu2 hnorm hout, card_range]
  have hUN : tp 80 R.u ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))) := by
    refine mem_normalizer_iff.2 fun p => ⟨fun hp => hnorm p hp, fun hp => ?_⟩
    have := hnorm _ hp
    have e : tp 80 R.u * (tp 80 R.u * p * (tp 80 R.u)⁻¹) * (tp 80 R.u)⁻¹ = p := by
      rw [hUi]
      calc tp 80 R.u * (tp 80 R.u * p * tp 80 R.u) * tp 80 R.u =
          (tp 80 R.u * tp 80 R.u) * p * (tp 80 R.u * tp 80 R.u) := by group
        _ = p := by rw [hUU, one_mul, mul_one]
    rwa [e] at this
  have hcover := cover_of_sylow (reps := {x | ∃ r ∈ R.rows, x = tp 80 r.row.rep}) hUN hSH
    (by rw [hScard, hcardR, fac_two]; norm_num)
    (fun s hs hs2 => by
      obtain ⟨r, hr, g, hg', e⟩ := htest s hs hs2
      exact ⟨_, ⟨r, hr, rfl⟩, g, hg', e⟩)
    (by
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨r', hr', g, hg', e⟩ := hUcl r hr
      exact ⟨_, ⟨r', hr', rfl⟩, g, hg', e⟩)
  have h1 : CFSG.Sporadic.Th.Rep 80 R.u (tp 80 R.u) := by
    rw [htpU]
    exact hrepU
  refine ⟨h1, rep_invT h1 hinv, hu2, hout, hnorm, hmemR, hrow (htpU ▸ hout), ?_⟩
  · intro τ hτ hτ2
    obtain ⟨_, ⟨r, hr, rfl⟩, g, hg', e⟩ := hcover τ hτ hτ2
    exact ⟨r, hr, g, hg', e⟩

end CertificateChecks.KernelP1L43

end
