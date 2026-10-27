module

public import Certificates.Kernel.P1L43.Runs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.PGroup
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecD
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Transport
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

set_option maxRecDepth 400000

public section


namespace CertificateChecks.KernelP1L43

open CFSG.ComponentClassification.HarrisLit CFSG.ComponentClassification.HarrisLit.P1
  CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.ArrEnum CFSG.KC.OrbFind
  CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.Certificates Subgroup
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

local notation "𝒞" t:max => (pi.range ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 80))))

noncomputable def ppn (n w P : ℕ) : Equiv.Perm (Fin n) :=
  CFSG.Monster.B.Co2.permOfArr n (unpack n w P)

theorem prep_ppn {n w P Q : ℕ} (h : permOK n w (mask w) (n * w) P Q = true) :
    PRep n w P (ppn n w P) :=
  prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr (isInvA_unpack h)).1

theorem gfacts {n w N ng : ℕ} {ps : List ℕ} {G GI T E D S : ℕ → ℕ} (hn : n < 16777216)
    (hw : n + 1 < 2 ^ w) (hps : ∀ p ∈ ps, p < n) (hh : headK n w ng G GI = true)
    (hcl : ∀ i < N, closPtL n w ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn n w)
    (hK : distinctK N (fun i => pkeyK n w ps (T i)) S = true) :
    Nat.card (closure ((fun k => ppn n w (G k)) '' {k | k < ng})) = N ∧
      (∀ y ∈ closure ((fun k => ppn n w (G k)) '' {k | k < ng}), ∃ i < N, PRep n w (T i) y) ∧
      ∀ i < N, ∀ y, PRep n w (T i) y → y ∈ closure ((fun k => ppn n w (G k)) '' {k | k < ng}) := by
  have hn32 : n < 2 ^ 32 := lt_trans hn (by norm_num)
  have hg : ∀ k < ng, PRep n w (G k) (ppn n w (G k)) :=
    fun k hk => prep_ppn ((headK_spec hh).2 k hk).2.2
  have hid : PRep n w (T 0) 1 := by
    rw [h0]
    exact prep_pidn hn hw
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ := leftOrb_reps (g := fun k => ppn n w (G k)) hn32 hg
    hcl htr hN hid hps hK
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) (fun _ _ h => h)
    (fun k => ppn n w (G k)) c ⟨0, hN, hc0⟩ hmem hcl' hinj
  refine ⟨hcard, fun y hy => ?_, fun i hi y hy => ?_⟩
  · obtain ⟨i, hi, e⟩ := hall y hy
    have e' : c i = y := e
    exact ⟨i, hi, by rw [← e']; exact hc i hi⟩
  · rw [prep_eq hy (hc i hi)]
    exact hmem i hi

theorem gf {N ng : ℕ} {G GI T E D S : ℕ → ℕ} (hh : headK 80 7 ng G GI = true)
    (hcl : ∀ i < N, closPtL 80 7 ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn 80 7)
    (hK : distinctK N (fun i => pkeyK 80 7 ps (T i)) S = true) :
    Nat.card (closure ((fun k => pp (G k)) '' {k | k < ng})) = N ∧
      (∀ y ∈ closure ((fun k => pp (G k)) '' {k | k < ng}), ∃ i < N, PRep 80 7 (T i) y) ∧
      ∀ i < N, ∀ y, PRep 80 7 (T i) y → y ∈ closure ((fun k => pp (G k)) '' {k | k < ng}) :=
  gfacts (by norm_num) (by norm_num) ps_lt hh hcl htr hN h0 hK

theorem prep_gen {ng : ℕ} {G GI : ℕ → ℕ} (hh : headK 80 7 ng G GI = true) :
    ∀ k < ng, PRep 80 7 (G k) (pp (G k)) ∧ PRep 80 7 (GI k) (pp (G k))⁻¹ := by
  intro k hk
  have h1 := prep_pp ((headK_spec hh).2 k hk).2.2
  exact ⟨h1, prep_inv h1 ((headK_spec hh).2 k hk).2.2⟩

theorem img2 {X : Type*} (f : ℕ → X) : f '' {k | k < 2} = {f 0, f 1} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem cent_facts {P M N ng : ℕ} {Uo : Option ℕ} {G GI : ℕ → ℕ} (hsi : selfInv P = true)
    (hrow : rowK P Uo G ng = true) (hh : headK 80 7 ng G GI = true)
    (hcard : Nat.card (closure ((fun k => pp (G k)) '' {k | k < ng})) = N)
    (hcls : M * Nat.card ↥(𝒞 (pp P)) = 6065280) (hMN : M * N = 6065280) :
    closure ((fun k => pp (G k)) '' {k | k < ng}) = 𝒞 (pp P) ∧ Nat.card ↥(𝒞 (pp P)) = N := by
  have hP := prep_si hsi
  unfold rowK at hrow
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hrow
  obtain ⟨-, -, hgen⟩ := hrow
  rw [CFSG.KS.Raw.Orb.allN_iff] at hgen
  have hpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h] at hMN
      omega
    · exact h
  have hC : Nat.card ↥(𝒞 (pp P)) = N := Nat.eq_of_mul_eq_mul_left hpos (hcls.trans hMN.symm)
  refine ⟨Subgroup.eq_of_le_of_card_ge ?_ (by rw [hC, hcard]), hC⟩
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have h2 := hgen k hk
  rw [Bool.and_eq_true] at h2
  have hG := (prep_gen hh k hk).1
  exact mem_inf.2 ⟨mem_of_sP hG h2.1, mem_centralizer_singleton_iff.2 (comm_of_cm hG hP h2.2)⟩

theorem norm_facts {P ng N nc : ℕ} {G GI T S C CI : ℕ → ℕ} (hsi : selfInv P = true)
    (hn : normK P G ng N T S C CI nc = true) (hhG : headK 80 7 ng G GI = true)
    (hpts : ∀ i < N, ∀ y, PRep 80 7 (T i) y → y ∈ closure ((fun k => pp (G k)) '' {k | k < ng}))
    (hhC : headK 80 7 nc C CI = true) :
    closure ((fun k => pp (G k)) '' {k | k < ng}) ≤ 𝒞 (pp P) ∧
      closure ((fun c => pp (C c)) '' {c | c < nc}) ≤
        normalizer (closure ((fun k => pp (G k)) '' {k | k < ng}) : Set (Equiv.Perm (Fin 80))) := by
  have hP := prep_si hsi
  unfold normK at hn
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.allN_iff,
    CFSG.KS.Raw.Orb.allN_iff] at hn
  obtain ⟨h1, h2⟩ := hn
  set L := closure ((fun k => pp (G k)) '' {k | k < ng}) with hL
  have hgen : ∀ c < nc, ∀ x ∈ L, pp (C c) * x * (pp (C c))⁻¹ ∈ L := by
    intro c hc x hx
    have hle : L ≤ L.comap (MulAut.conj (pp (C c))).toMonoidHom := by
      conv_lhs => rw [hL]
      rw [closure_le]
      rintro _ ⟨k, hk, rfl⟩
      change pp (C c) * pp (G k) * (pp (C c))⁻¹ ∈ L
      have hm := CFSG.KS.Raw.Orb.allN_iff.1 (h2 c hc) k hk
      obtain ⟨j, hj, e⟩ := memK_spec hm
      have hp : PRep 80 7 (pc (C c) (pc (G k) (CI c))) (pp (C c) * (pp (G k) * (pp (C c))⁻¹)) :=
        prep_pcomp hn80 (prep_gen hhC c hc).1
          (prep_pcomp hn80 (prep_gen hhG k hk).1 (prep_gen hhC c hc).2)
      rw [← e, ← mul_assoc] at hp
      exact hpts j hj _ hp
    exact hle hx
  refine ⟨?_, CFSG.ComponentClassification.Sol76.le_normalizer_of_forall_conj_mem
    fun c hc x hx => ?_⟩
  · rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have h3 := h1 k hk
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h3
    have hG := (prep_gen hhG k hk).1
    exact mem_inf.2 ⟨mem_of_sP hG h3.1, mem_centralizer_singleton_iff.2 (comm_of_cm hG hP h3.2)⟩
  · refine conj_closed (s := (fun c => pp (C c)) '' {c | c < nc}) (O := (L : Set _)) ?_ c hc x hx
    rintro _ ⟨c', hc', rfl⟩ y hy
    exact hgen c' hc' y hy

theorem relIndex_eq {K C : Subgroup (Equiv.Perm (Fin 80))} {a r : ℕ} (hKC : K ≤ C)
    (hK : Nat.card K = a) (hC : Nat.card C = r * a) (ha : 0 < a) : K.relIndex C = r := by
  have h := CFSG.ComponentClassification.HarrisLit.P1.relIndex_mul_card_of_le hKC
  rw [hK, hC] at h
  exact Nat.eq_of_mul_eq_mul_right ha h

theorem not_mem_of_rowK {P U ng : ℕ} {G : ℕ → ℕ} {σ : Equiv.Perm (Fin 80)}
    (hsi : selfInv P = true) (hrow : rowK P (some U) G ng = true) (hU : PRep 80 7 U σ)
    (hσ : σ ∉ pi.range) : pp P ∉ pi.range := by
  unfold rowK at hrow
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hrow
  obtain ⟨-, hmem, -⟩ := hrow
  change sP (pc P U) = true at hmem
  have hin := mem_of_sP (prep_pcomp hn80 (prep_si hsi) hU) hmem
  intro hPA
  apply hσ
  have e : σ = (pp P)⁻¹ * (pp P * σ) := by group
  rw [e]
  exact mul_mem (inv_mem hPA) hin

theorem mem_normalizer_of_sq {u : Equiv.Perm (Fin 80)} (hu : u ^ 2 = 1)
    (hn : ∀ p ∈ pi.range, u * p * u⁻¹ ∈ pi.range) :
    u ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))) := by
  have hUi : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq, hu])
  refine mem_normalizer_iff.2 fun p => ⟨fun hp => hn p hp, fun hp => ?_⟩
  have h1 := hn _ hp
  have e : u * (u * p * u⁻¹) * u⁻¹ = p := by
    rw [hUi]
    calc u * (u * p * u) * u = (u * u) * p * (u * u) := by group
      _ = p := by rw [← sq, hu, one_mul, mul_one]
  rwa [e] at h1

theorem outer_facts {R : Run} {U : ℕ} (hR : RunFacts pi.range R) (hb : bindT R.u U = true)
    (hs : selfInv U = true) :
    tp 80 R.u = pp U ∧ pp U ∉ pi.range ∧ pp U * pp U = 1 ∧
      pp U ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))) := by
  have e := tpR hb hs
  refine ⟨e, e ▸ hR.uout, pp_mul_self hs, ?_⟩
  rw [← e]
  exact mem_normalizer_of_sq hR.u2 hR.unorm

theorem outD : tp 80 runuD.u = pp UD ∧ pp UD ∉ pi.range ∧ pp UD * pp UD = 1 ∧
    pp UD ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))) :=
  outer_facts runFactsD binds.1 (si (by simp))

theorem outS : tp 80 runuS.u = pp US ∧ pp US ∉ pi.range ∧ pp US * pp US = 1 ∧
    pp US ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))) :=
  outer_facts runFactsS binds.2.1 (si (by simp))

theorem outDS : tp 80 runuDS.u = pp UDS ∧ pp UDS ∉ pi.range ∧ pp UDS * pp UDS = 1 ∧
    pp UDS ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))) :=
  outer_facts runFactsDS binds.2.2.1 (si (by simp))

theorem fac2 (a m : ℕ) (hm : ¬ 2 ∣ m) : (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem config_core {P W ng N a m : ℕ} {G GI T Lp : ℕ → ℕ} {mem : ℕ → Bool}
    {L : Subgroup (Equiv.Perm (Fin 80))} {w : Equiv.Perm (Fin 80)} (hsi : selfInv P = true)
    (hLeq : Q81.oddPart (𝒞 (pp P)) = L) (hLp : ∀ l ∈ L, ∃ j < 360, PRep 80 7 (Lp j) l)
    (hmem : ∀ v, mem v = true → ∀ s, PRep 80 7 v s → A6Normal pi.range s)
    (hW : PRep 80 7 W w) (hwA : w ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))))
    (hwt : cm W P = true)
    (hgen : allN ng (fun k => bAnd(cm (G k) P, sP (G k) || sP (pc (G k) W))) = true)
    (hh : headK 80 7 ng G GI = true)
    (hTcard : Nat.card (closure ((fun k => pp (G k)) '' {k | k < ng})) = 2 ^ a)
    (hTpts : ∀ y ∈ closure ((fun k => pp (G k)) '' {k | k < ng}), ∃ i < N, PRep 80 7 (T i) y)
    (hCw : Nat.card ↥(𝒞 (pp P) ⊔ zpowers w) = 2 ^ a * m) (hm : ¬ 2 ∣ m)
    (hconf : configK mem Lp N T = true) {v : Equiv.Perm (Fin 80)} (hv2 : orderOf v = 2)
    (hvt : v * pp P = pp P * v) (hvw : v * w⁻¹ ∈ pi.range)
    (hl : ∃ l ∈ L, orderOf l = 2 ∧ orderOf (v * l) = 8) : A6Normal pi.range v := by
  have hP := prep_si hsi
  have hwt' : w * pp P = pp P * w := comm_of_cm hW hP hwt
  rw [CFSG.KS.Raw.Orb.allN_iff] at hgen
  have hTD : closure ((fun k => pp (G k)) '' {k | k < ng}) ≤ 𝒞 (pp P) ⊔ zpowers w := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have h2 := hgen k hk
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.or_eq_true] at h2
    have hG := (prep_gen hh k hk).1
    have hgt := comm_of_cm hG hP h2.1
    rcases h2.2 with h | h
    · exact mem_sup_left (mem_inf.2 ⟨mem_of_sP hG h, mem_centralizer_singleton_iff.2 hgt⟩)
    · have hgw : pp (G k) * w ∈ 𝒞 (pp P) := by
        refine mem_inf.2 ⟨mem_of_sP (prep_pcomp hn80 hG hW) h, ?_⟩
        rw [mem_centralizer_singleton_iff]
        exact Commute.mul_left (a := pp (G k)) hgt hwt'
      have e : pp (G k) = pp (G k) * w * w⁻¹ := by group
      change pp (G k) ∈ 𝒞 (pp P) ⊔ zpowers w
      rw [e]
      exact mul_mem (mem_sup_left hgw) (mem_sup_right (inv_mem (mem_zpowers w)))
  have htest : ∀ v ∈ closure ((fun k => pp (G k)) '' {k | k < ng}), orderOf v = 2 →
      (v ∈ pi.range ↔ w ∈ pi.range) → (∃ l ∈ L, orderOf l = 2 ∧ orderOf (v * l) = 8) →
      A6Normal pi.range v := by
    rintro v hvT hv2 - ⟨l, hlL, hl2, hl8⟩
    obtain ⟨i, hi, hPv⟩ := hTpts v hvT
    unfold configK at hconf
    rw [CFSG.KS.Raw.Orb.allN_iff] at hconf
    have h1 := hconf i hi
    rw [strictB_eq', (isInvK_iff hn80 hPv).2 hv2, Bool.not_true, Bool.false_or,
      Bool.or_eq_true] at h1
    rcases h1 with h | h
    · obtain ⟨j, hj, hPl⟩ := hLp l hlL
      have h3 := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
      have hvl : PRep 80 7 (pc (T i) (Lp j)) (v * l) := prep_pcomp hn80 hPv hPl
      rw [strictB_eq', CFSG.KS.Raw.Orb.bAnd_eq, (isInvK_iff hn80 hPl).2 hl2,
        (ord8K_iff hn80 hvl).2 hl8] at h3
      exact absurd h3 (by decide)
    · exact hmem _ h v hPv
  refine config_of_sylow hLeq hwA hwt' hTD (by rw [hTcard, hCw, fac2 a m hm]) htest hv2 hvt
    hvw hl

theorem config_inner {P ng N a m : ℕ} {G GI T Lp : ℕ → ℕ} {mem : ℕ → Bool}
    {L : Subgroup (Equiv.Perm (Fin 80))} (hsi : selfInv P = true)
    (hLeq : Q81.oddPart (𝒞 (pp P)) = L) (hLp : ∀ l ∈ L, ∃ j < 360, PRep 80 7 (Lp j) l)
    (hmem : ∀ v, mem v = true → ∀ s, PRep 80 7 v s → A6Normal pi.range s)
    (hc : cosetK P (pidn 80 7) none G ng = true) (hh : headK 80 7 ng G GI = true)
    (hTcard : Nat.card (closure ((fun k => pp (G k)) '' {k | k < ng})) = 2 ^ a)
    (hTpts : ∀ y ∈ closure ((fun k => pp (G k)) '' {k | k < ng}), ∃ i < N, PRep 80 7 (T i) y)
    (hC : Nat.card ↥(𝒞 (pp P)) = 2 ^ a * m) (hm : ¬ 2 ∣ m)
    (hconf : configK mem Lp N T = true) {v : Equiv.Perm (Fin 80)} (hv2 : orderOf v = 2)
    (hvt : v * pp P = pp P * v) (hvA : v ∈ pi.range)
    (hl : ∃ l ∈ L, orderOf l = 2 ∧ orderOf (v * l) = 8) : A6Normal pi.range v := by
  unfold cosetK at hc
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
    CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
  obtain ⟨hwt, -, -, hgen⟩ := hc
  have hW : PRep 80 7 (pidn 80 7) 1 := prep_pidn (by norm_num) (by norm_num)
  exact config_core hsi hLeq hLp hmem hW (one_mem _) hwt hgen hh hTcard hTpts
    (by rw [zpowers_one_eq_bot, sup_bot_eq, hC]) hm hconf hv2 hvt (by rwa [inv_one, mul_one]) hl

theorem config_outer {P W U ng N a m : ℕ} {G GI T Lp : ℕ → ℕ} {mem : ℕ → Bool}
    {L : Subgroup (Equiv.Perm (Fin 80))} {σ : Equiv.Perm (Fin 80)} (hsi : selfInv P = true)
    (hLeq : Q81.oddPart (𝒞 (pp P)) = L) (hLp : ∀ l ∈ L, ∃ j < 360, PRep 80 7 (Lp j) l)
    (hmem : ∀ v, mem v = true → ∀ s, PRep 80 7 v s → A6Normal pi.range s)
    {WI : ℕ} (hWs : permOK 80 7 (mask 7) (80 * 7) W WI = true)
    (hU : PRep 80 7 U σ) (hσ : σ ∉ pi.range) (hσσ : σ * σ = 1)
    (hσN : σ ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))))
    (hc : cosetK P W (some U) G ng = true) (hh : headK 80 7 ng G GI = true)
    (hTcard : Nat.card (closure ((fun k => pp (G k)) '' {k | k < ng})) = 2 ^ a)
    (hTpts : ∀ y ∈ closure ((fun k => pp (G k)) '' {k | k < ng}), ∃ i < N, PRep 80 7 (T i) y)
    (hC : 2 * Nat.card ↥(𝒞 (pp P)) = 2 ^ a * m) (hm : ¬ 2 ∣ m)
    (hconf : configK mem Lp N T = true) {v : Equiv.Perm (Fin 80)} (hv2 : orderOf v = 2)
    (hvt : v * pp P = pp P * v) (hvA : v * σ⁻¹ ∈ pi.range)
    (hl : ∃ l ∈ L, orderOf l = 2 ∧ orderOf (v * l) = 8) : A6Normal pi.range v := by
  have hP := prep_si hsi
  have hW := prep_pp hWs
  set w := pp W
  unfold cosetK at hc
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
    CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
  obtain ⟨hwt, hw2, hwU, hgen⟩ := hc
  change sP (pc W U) = true at hwU
  have hwσ : w * σ ∈ pi.range := mem_of_sP (prep_pcomp hn80 hW hU) hwU
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hwN : w ∈ normalizer (pi.range : Set (Equiv.Perm (Fin 80))) := by
    have e : w = w * σ * σ⁻¹ := by group
    rw [e]
    exact mul_mem (le_normalizer hwσ) (inv_mem hσN)
  have hwt' : w * pp P = pp P * w := comm_of_cm hW hP hwt
  have hwC : w ∉ 𝒞 (pp P) := by
    intro h
    apply hσ
    have e : σ = w⁻¹ * (w * σ) := by group
    rw [e]
    exact mul_mem (inv_mem (mem_inf.1 h).1) hwσ
  have hw2C : w ^ 2 ∈ 𝒞 (pp P) := by
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [sq]
      exact mem_of_sP (prep_pcomp hn80 hW hW) hw2
    · rw [mem_centralizer_singleton_iff, sq]
      exact Commute.mul_left (a := w) hwt' hwt'
  have hwNC : w ∈ normalizer
      ((𝒞 (pp P) : Subgroup (Equiv.Perm (Fin 80))) : Set (Equiv.Perm (Fin 80))) := by
    have hwtw : w * pp P * w⁻¹ = pp P := by rw [hwt', mul_inv_cancel_right]
    have hmap : (𝒞 (pp P)).map (MulAut.conj w).toMonoidHom = 𝒞 (pp P) := by
      rw [← inf_centralizer_conj_of_mem_normalizer pi.range hwN (pp P), hwtw]
    refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hmap]
      exact ⟨x, hx, by simp⟩
    · rw [← hmap] at hx
      obtain ⟨y, hy, e⟩ := hx
      have e' : y = x := by simpa using e
      rwa [← e']
  have hCw : Nat.card ↥(𝒞 (pp P) ⊔ zpowers w) = 2 ^ a * m := by
    rw [CFSG.EvenSporadicStandard.HNRecog.Harada.card_sup_zpowers_of_sq_mem hwNC hwC hw2C, hC]
  have hvw : v * w⁻¹ ∈ pi.range := by
    have e : v * w⁻¹ = v * σ⁻¹ * (w * σ⁻¹)⁻¹ := by group
    rw [e, hσi]
    rw [hσi] at hvA
    exact mul_mem hvA (inv_mem hwσ)
  exact config_core hsi hLeq hLp hmem hW hwN hwt hgen hh hTcard hTpts hCw hm hconf hv2 hvt hvw hl

theorem prep_pair {D L Y : ℕ} {x : Equiv.Perm (Fin 80)} {y : Equiv.Perm (Fin 6)}
    (hd : diagK D L Y = true) (hL : PRep 80 7 L x) (hY : PRep 6 3 Y y) :
    PRep 86 7 D (pairHom 80 (x, y)) := by
  unfold diagK at hd
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, CFSG.KS.Raw.Orb.allN_iff,
    CFSG.KS.Raw.Orb.allN_iff] at hd
  obtain ⟨h1, h2⟩ := hd
  intro z
  obtain ⟨i, hi⟩ := z
  change pg 7 (mask 7) D i = (finSumFinEquiv (Equiv.Perm.sumCongr x y
    (finSumFinEquiv.symm (⟨i, hi⟩ : Fin (80 + 6)))) : Fin (80 + 6)).val
  by_cases hin : i < 80
  · have he : (⟨i, hi⟩ : Fin (80 + 6)) = Fin.castAdd 6 ⟨i, hin⟩ := rfl
    rw [he, finSumFinEquiv_symm_apply_castAdd, Equiv.Perm.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, Fin.val_castAdd, ← hL ⟨i, hin⟩]
    exact Nat.eq_of_beq_eq_true (h1 i hin)
  · have hj : i - 80 < 6 := by omega
    have he : (⟨i, hi⟩ : Fin (80 + 6)) = Fin.natAdd 80 ⟨i - 80, hj⟩ :=
      Fin.ext (by simp only [Fin.val_natAdd]; omega)
    rw [he, finSumFinEquiv_symm_apply_natAdd, Equiv.Perm.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, Fin.val_natAdd, ← hY ⟨i - 80, hj⟩]
    have h3 : pg 7 (mask 7) D (80 + (i - 80)) = 80 + pg 3 (mask 3) Y (i - 80) :=
      Nat.eq_of_beq_eq_true (h2 (i - 80) hj)
    have e : 80 + (i - 80) = i := by omega
    rw [e] at h3
    exact h3

theorem iso_of {Lng Dng Ang : ℕ} {LG LGI DG DGI AG AGI : ℕ → ℕ} (hL2 : Lng = 2) (hD2 : Dng = 2)
    (hA2 : Ang = 2) (hhL : headK 80 7 Lng LG LGI = true)
    (hLc : Nat.card (closure ((fun k => pp (LG k)) '' {k | k < Lng})) = 360)
    (hhD : headK 86 7 Dng DG DGI = true)
    (hDc : Nat.card (closure ((fun k => ppn 86 7 (DG k)) '' {k | k < Dng})) = 360)
    (hhA : headK 6 3 Ang AG AGI = true)
    (hAc : Nat.card (closure ((fun k => ppn 6 3 (AG k)) '' {k | k < Ang})) = 360)
    (hoddA : allN 2 (fun k => oddK 6 3 (AG k)) = true)
    (hdiag : allN 2 (fun k => diagK (DG k) (LG k) (AG k)) = true) :
    Nonempty (↥(closure ((fun k => pp (LG k)) '' {k | k < Lng})) ≃* alternatingGroup (Fin 6)) := by
  subst hL2 hD2 hA2
  have hA : ∀ k < 2, PRep 6 3 (AG k) (ppn 6 3 (AG k)) :=
    fun k hk => prep_ppn ((headK_spec hhA).2 k hk).2.2
  have hD : ∀ k < 2, PRep 86 7 (DG k) (ppn 86 7 (DG k)) :=
    fun k hk => prep_ppn ((headK_spec hhD).2 k hk).2.2
  have e : ∀ k < 2, ppn 86 7 (DG k) = pairHom 80 (pp (LG k), ppn 6 3 (AG k)) := fun k hk =>
    prep_eq (hD k hk) (prep_pair (CFSG.KS.Raw.Orb.allN_iff.1 hdiag k hk) (prep_gen hhL k hk).1
      (hA k hk))
  rw [img2] at hLc hDc hAc
  rw [e 0 (by norm_num), e 1 (by norm_num)] at hDc
  rw [img2]
  exact nonempty_equiv_alternating_six_of_card
    (oddK_spec (by norm_num) (hA 0 (by norm_num)) (CFSG.KS.Raw.Orb.allN_iff.1 hoddA 0 (by norm_num)))
    (oddK_spec (by norm_num) (hA 1 (by norm_num)) (CFSG.KS.Raw.Orb.allN_iff.1 hoddA 1 (by norm_num)))
    hAc hLc hDc

theorem a6_core {P Lng LN Cng a : ℕ} {LG LGI LT LS CG CGI : ℕ → ℕ} (hsi : selfInv P = true)
    (hn : normK P LG Lng LN LT LS CG CGI Cng = true) (hhL : headK 80 7 Lng LG LGI = true)
    (hLc : Nat.card (closure ((fun k => pp (LG k)) '' {k | k < Lng})) = 360)
    (hLpts : ∀ i < LN, ∀ y, PRep 80 7 (LT i) y →
      y ∈ closure ((fun k => pp (LG k)) '' {k | k < Lng}))
    (hhC : headK 80 7 Cng CG CGI = true)
    (hC : closure ((fun c => pp (CG c)) '' {c | c < Cng}) = 𝒞 (pp P))
    (hCc : Nat.card ↥(𝒞 (pp P)) = 2 ^ a * 360)
    (hodd : allN 2 (fun k => oddK 80 7 (LG k)) = true) (hLng : Lng = 2) :
    closure ((fun k => pp (LG k)) '' {k | k < Lng}) ≤ 𝒞 (pp P) ∧
      𝒞 (pp P) ≤ normalizer (closure ((fun k => pp (LG k)) '' {k | k < Lng}) :
        Set (Equiv.Perm (Fin 80))) ∧
      (∃ b, (closure ((fun k => pp (LG k)) '' {k | k < Lng})).relIndex (𝒞 (pp P)) = 2 ^ b) ∧
      closure ((fun k => pp (LG k)) '' {k | k < Lng}) ≤ Q81.oddPart (𝒞 (pp P)) := by
  subst hLng
  obtain ⟨hle, hN⟩ := norm_facts hsi hn hhL hLpts hhC
  rw [hC] at hN
  refine ⟨hle, hN, ⟨a, relIndex_eq hle hLc hCc (by norm_num)⟩, ?_⟩
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact Q81.mem_oddPart (hle (subset_closure ⟨k, hk, rfl⟩))
    (oddK_spec hn80 (prep_gen hhL k hk).1 (CFSG.KS.Raw.Orb.allN_iff.1 hodd k hk))

structure A6F (t : Equiv.Perm (Fin 80)) (L : Subgroup (Equiv.Perm (Fin 80))) (Lp : ℕ → ℕ) :
    Prop where
  le : L ≤ 𝒞 t
  norm : 𝒞 t ≤ normalizer (L : Set (Equiv.Perm (Fin 80)))
  card : Nat.card L = 360
  pow : ∃ a, L.relIndex (𝒞 t) = 2 ^ a
  odd : L ≤ Q81.oddPart (𝒞 t)
  iso : Nonempty (↥L ≃* alternatingGroup (Fin 6))
  pts : ∀ l ∈ L, ∃ j < 360, PRep 80 7 (Lp j) l

theorem A6F.oddPart_eq {t : Equiv.Perm (Fin 80)} {L : Subgroup (Equiv.Perm (Fin 80))}
    {Lp : ℕ → ℕ} (h : A6F t L Lp) : Q81.oddPart (𝒞 t) = L :=
  oddPart_eq_of_le h.le h.norm h.pow h.odd

theorem A6F.a6Normal {t : Equiv.Perm (Fin 80)} {L : Subgroup (Equiv.Perm (Fin 80))}
    {Lp : ℕ → ℕ} (h : A6F t L Lp) : A6Normal pi.range t :=
  a6Normal_of_le h.le h.norm h.iso

theorem card_of_cls {N M : ℕ} {t : Equiv.Perm (Fin 80)}
    (h : N * Nat.card ↥(𝒞 t) = 6065280) (hN : N * M = 6065280) : Nat.card ↥(𝒞 t) = M := by
  have hpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0] at hN
      omega
    · exact h0
  exact Nat.eq_of_mul_eq_mul_left hpos (h.trans hN.symm)

theorem centD0 : closure ((fun k => pp (CD0.G k)) '' {k | k < CD0.ng}) =
    𝒞 (pp (K2106.T K2106.r0)) ∧ Nat.card ↥(𝒞 (pp (K2106.T K2106.r0))) = CD0.N :=
  cent_facts (si (by simp)) rows.1 CD0.h
    (gf CD0.h (fun i hi => CD0.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CD0.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
      CD0.k).1 c2106_0.2.1 (by decide)

theorem centD2 : closure ((fun k => pp (CD2.G k)) '' {k | k < CD2.ng}) =
    𝒞 (pp (K5265.T K5265.r0)) ∧ Nat.card ↥(𝒞 (pp (K5265.T K5265.r0))) = CD2.N :=
  cent_facts (si (by simp)) rows.2.2.1 CD2.h
    (gf CD2.h (fun i hi => CD2.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CD2.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
      CD2.k).1 c5265_0.2.1 (by decide)

theorem centDS2 : closure ((fun k => pp (CDS2.G k)) '' {k | k < CDS2.ng}) =
    𝒞 (pp (K8424.T K8424.r0)) ∧ Nat.card ↥(𝒞 (pp (K8424.T K8424.r0))) = CDS2.N :=
  cent_facts (si (by simp)) rows.2.2.2.2.2.2.2.2.2.2 CDS2.h
    (gf CDS2.h (fun i hi => CDS2.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => CDS2.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
      CDS2.k).1 c8424.2.1 (by decide)

theorem fD0 : A6F (pp (K2106.T K2106.r0)) (closure ((fun k => pp (LD0.G k)) '' {k | k < LD0.ng}))
    LD0.T := by
  obtain ⟨hn, -, hoL, -, hoA, hL2, -, hD2, -, hA2, hd, -⟩ := a6K
  have hgL := gf LD0.h (fun i hi => LD0.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => LD0.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) LD0.k
  have hgD := gfacts (n := 86) (w := 7) (by norm_num) (by norm_num)
    (fun p hp => lt_trans (ps_lt p hp) (by norm_num)) DD0.h
    (fun i hi => DD0.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => DD0.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) DD0.k
  have hgA := gfacts (n := 6) (w := 3) (by norm_num) (by norm_num) (by decide) A6.h
    (fun i hi => A6.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => A6.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) A6.k
  have hLc : Nat.card (closure ((fun k => pp (LD0.G k)) '' {k | k < LD0.ng})) = 360 := hgL.1
  obtain ⟨hle, hnorm, hpow, hodd⟩ := a6_core (a := 3) (si (by simp)) hn LD0.h hLc hgL.2.2 CD0.h
    centD0.1 (by rw [centD0.2]; rfl) hoL hL2
  exact ⟨hle, hnorm, hLc, hpow, hodd, iso_of hL2 hD2 hA2 LD0.h hLc DD0.h hgD.1 A6.h hgA.1 hoA hd,
    hgL.2.1⟩

theorem fDS2 : A6F (pp (K8424.T K8424.r0))
    (closure ((fun k => pp (LDS2.G k)) '' {k | k < LDS2.ng})) LDS2.T := by
  obtain ⟨-, hn, -, hoL, hoA, -, hL2, -, hD2, hA2, -, hd⟩ := a6K
  have hgL := gf LDS2.h (fun i hi => LDS2.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => LDS2.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    LDS2.k
  have hgD := gfacts (n := 86) (w := 7) (by norm_num) (by norm_num)
    (fun p hp => lt_trans (ps_lt p hp) (by norm_num)) DDS2.h
    (fun i hi => DDS2.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => DDS2.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    DDS2.k
  have hgA := gfacts (n := 6) (w := 3) (by norm_num) (by norm_num) (by decide) A6.h
    (fun i hi => A6.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => A6.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) A6.k
  have hLc : Nat.card (closure ((fun k => pp (LDS2.G k)) '' {k | k < LDS2.ng})) = 360 := hgL.1
  obtain ⟨hle, hnorm, hpow, hodd⟩ := a6_core (a := 1) (si (by simp)) hn LDS2.h hLc hgL.2.2
    CDS2.h centDS2.1 (by rw [centDS2.2]; rfl) hoL hL2
  exact ⟨hle, hnorm, hLc, hpow, hodd,
    iso_of hL2 hD2 hA2 LDS2.h hLc DDS2.h hgD.1 A6.h hgA.1 hoA hd, hgL.2.1⟩

theorem good_a6 : ∀ v, good v = true → ∀ s, PRep 80 7 v s → A6Normal pi.range s := by
  intro v hv s hs
  unfold good at hv
  rw [Bool.or_eq_true] at hv
  rcases hv with h | h
  · obtain ⟨g, hg, rfl⟩ := mem_class c2106_0 h hs
    exact a6Normal_conj (le_normalizer hg) fD0.a6Normal
  · obtain ⟨g, hg, rfl⟩ := mem_class c8424 h hs
    exact a6Normal_conj (le_normalizer hg) fDS2.a6Normal

noncomputable def pinv (t : Table) : ℕ := pk (natArr (invT 80 t))

theorem wperms :
    permOK 80 7 (mask 7) (80 * 7) wD1 (pinv (tm 29414775)) = true ∧
    permOK 80 7 (mask 7) (80 * 7) wD2 (pinv (ts 25614936)) = true ∧
    permOK 80 7 (mask 7) (80 * 7) wD3 (pinv (ts 24033253)) = true ∧
    permOK 80 7 (mask 7) (80 * 7) wDS1 (pinv (tm 21158344)) = true ∧
    permOK 80 7 (mask 7) (80 * 7) wDS2 (pinv (ts 7406221)) = true ∧
    permOK 80 7 (mask 7) (80 * 7) wDS3 (pinv (ts 14204479)) = true := by
  decide +kernel

theorem siU : selfInv UD = true ∧ selfInv US = true ∧ selfInv UDS = true :=
  ⟨si (by simp), si (by simp), si (by simp)⟩

theorem config2106 : ∀ v ∈ l43Model.T.range, orderOf v = 2 →
    v * pp (K2106.T K2106.r0) = pp (K2106.T K2106.r0) * v →
    (∃ l ∈ closure ((fun k => pp (LD0.G k)) '' {k | k < LD0.ng}), orderOf l = 2 ∧
      orderOf (v * l) = 8) → A6Normal pi.range v := by
  rintro _ ⟨α, rfl⟩ hv2 hvt hl
  have hsi : selfInv (K2106.T K2106.r0) = true := si (by simp)
  have hLeq := fD0.oddPart_eq
  have hC := centD0.2
  obtain ⟨c0, c1, c2, c3, -⟩ := cosets
  obtain ⟨w1, w2, w3, -⟩ := wperms
  have g0 := gf TD00.h (fun i hi => TD00.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => TD00.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) TD00.k
  have g1 := gf TD01.h (fun i hi => TD01.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => TD01.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) TD01.k
  have g2 := gf TD02.h (fun i hi => TD02.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => TD02.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) TD02.k
  have g3 := gf TD03.h (fun i hi => TD03.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => TD03.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) TD03.k
  rcases l43_cos α with h | ⟨R, hR, h⟩ | ⟨u, hu, -⟩
  · exact config_inner (a := 6) (m := 45) hsi hLeq fD0.pts good_a6 c0 TD00.h g0.1 g0.2.1
      (by rw [hC]; rfl) (by decide) configD0 hv2 hvt h hl
  · simp only [l43Runs, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · rw [outD.1] at h
      exact config_outer (a := 7) (m := 45) hsi hLeq fD0.pts good_a6 w1 (prep_si siU.1)
        outD.2.1 outD.2.2.1 outD.2.2.2 c1 TD01.h g1.1 g1.2.1 (by rw [hC]; rfl) (by decide)
        configD1 hv2 hvt h hl
    · rw [outS.1] at h
      exact config_outer (a := 7) (m := 45) hsi hLeq fD0.pts good_a6 w2 (prep_si siU.2.1)
        outS.2.1 outS.2.2.1 outS.2.2.2 c2 TD02.h g2.1 g2.2.1 (by rw [hC]; rfl) (by decide)
        configD2 hv2 hvt h hl
    · rw [outDS.1] at h
      exact config_outer (a := 7) (m := 45) hsi hLeq fD0.pts good_a6 w3 (prep_si siU.2.2)
        outDS.2.1 outDS.2.2.1 outDS.2.2.2 c3 TD03.h g3.1 g3.2.1 (by rw [hC]; rfl) (by decide)
        configD3 hv2 hvt h hl
  · simp at hu

theorem config8424 : ∀ v ∈ l43Model.T.range, orderOf v = 2 →
    v * pp (K8424.T K8424.r0) = pp (K8424.T K8424.r0) * v →
    (∃ l ∈ closure ((fun k => pp (LDS2.G k)) '' {k | k < LDS2.ng}), orderOf l = 2 ∧
      orderOf (v * l) = 8) → A6Normal pi.range v := by
  rintro _ ⟨α, rfl⟩ hv2 hvt hl
  have hsi : selfInv (K8424.T K8424.r0) = true := si (by simp)
  have hLeq := fDS2.oddPart_eq
  have hC := centDS2.2
  obtain ⟨-, -, -, -, c0, c1, c2, c3⟩ := cosets
  obtain ⟨-, -, -, w1, w2, w3⟩ := wperms
  have g0 := gf TDS20.h (fun i hi => TDS20.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => TDS20.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    TDS20.k
  have g1 := gf TDS21.h (fun i hi => TDS21.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => TDS21.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    TDS21.k
  have g2 := gf TDS22.h (fun i hi => TDS22.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => TDS22.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    TDS22.k
  have g3 := gf TDS23.h (fun i hi => TDS23.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => TDS23.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    TDS23.k
  rcases l43_cos α with h | ⟨R, hR, h⟩ | ⟨u, hu, -⟩
  · exact config_inner (a := 4) (m := 45) hsi hLeq fDS2.pts good_a6 c0 TDS20.h g0.1 g0.2.1
      (by rw [hC]; rfl) (by decide) configDS0 hv2 hvt h hl
  · simp only [l43Runs, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · rw [outD.1] at h
      exact config_outer (a := 5) (m := 45) hsi hLeq fDS2.pts good_a6 w1 (prep_si siU.1)
        outD.2.1 outD.2.2.1 outD.2.2.2 c1 TDS21.h g1.1 g1.2.1 (by rw [hC]; rfl) (by decide)
        configDS1 hv2 hvt h hl
    · rw [outS.1] at h
      exact config_outer (a := 5) (m := 45) hsi hLeq fDS2.pts good_a6 w2 (prep_si siU.2.1)
        outS.2.1 outS.2.2.1 outS.2.2.2 c2 TDS22.h g2.1 g2.2.1 (by rw [hC]; rfl) (by decide)
        configDS2 hv2 hvt h hl
    · rw [outDS.1] at h
      exact config_outer (a := 5) (m := 45) hsi hLeq fDS2.pts good_a6 w3 (prep_si siU.2.2)
        outDS.2.1 outDS.2.2.1 outDS.2.2.2 c3 TDS23.h g3.1 g3.2.1 (by rw [hC]; rfl) (by decide)
        configDS3 hv2 hvt h hl
  · simp at hu

noncomputable def l43Reps : Set (Equiv.Perm (Fin 80)) :=
  {pp (K2106.T K2106.r0), pp (K5265.T K5265.r0), pp (K1080.T K1080.r0),
    pp (K10530.T K10530.r0), pp (K117a.T K117a.r0), pp (K117b.T K117b.r0),
    pp (K8424.T K8424.r0)}

theorem rep2106 : RepFacts pi.range l43Model.T.range (pp (K2106.T K2106.r0)) :=
  .a6 _ fD0.le fD0.norm fD0.card fD0.pow fD0.odd fD0.iso config2106

theorem rep8424 : RepFacts pi.range l43Model.T.range (pp (K8424.T K8424.r0)) :=
  .a6 _ fDS2.le fDS2.norm fDS2.card fDS2.pow fDS2.odd fDS2.iso config8424

theorem rep5265 : RepFacts pi.range l43Model.T.range (pp (K5265.T K5265.r0)) := by
  have hgK := gf KD2.h (fun i hi => KD2.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => KD2.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) KD2.k
  obtain ⟨hle, hN⟩ := norm_facts (si (by simp)) smallK KD2.h hgK.2.2 CD2.h
  rw [centD2.1] at hN
  exact .small _ hle hN (by rw [hgK.1]; decide)
    ⟨2, relIndex_eq hle hgK.1 (by rw [centD2.2]; rfl) (by decide)⟩ (by rw [centD2.2]; decide)

theorem rep1080 : RepFacts pi.range l43Model.T.range (pp (K1080.T K1080.r0)) :=
  .noA6 (not_mem_of_rowK (si (by simp)) rows.2.1 (prep_si siU.1) outD.2.1)
    fun L hLC hL _ => no360_of_not_dvd
      (by rw [card_of_cls c1080.2.1 (M := 5616) (by decide)]; decide) L hLC hL

theorem rep10530 : RepFacts pi.range l43Model.T.range (pp (K10530.T K10530.r0)) :=
  .noA6 (not_mem_of_rowK (si (by simp)) rows.2.2.2.2.1 (prep_si siU.2.1) outS.2.1)
    fun L hLC hL _ => no360_of_not_dvd
      (by rw [card_of_cls c10530.2.1 (M := 576) (by decide)]; decide) L hLC hL

theorem five_of {P ng : ℕ} {G GI : ℕ → ℕ} (hsi : selfInv P = true)
    (hf : allN ng (fun k => bAnd(sP (G k), bAnd(cm (G k) P, ord5K 80 7 (G k)))) = true)
    (hh : headK 80 7 ng G GI = true) :
    ∀ g ∈ (fun k => pp (G k)) '' {k | k < ng}, g ∈ 𝒞 (pp P) ∧ g ^ 5 = 1 := by
  rintro _ ⟨k, hk, rfl⟩
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hf k hk
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  have hG := (prep_gen hh k hk).1
  exact ⟨mem_inf.2 ⟨mem_of_sP hG h.1,
    mem_centralizer_singleton_iff.2 (comm_of_cm hG (prep_si hsi) h.2.1)⟩,
    (ord5K_spec hn80 hG h.2.2).1⟩

theorem rep117a : RepFacts pi.range l43Model.T.range (pp (K117a.T K117a.r0)) := by
  have hC := card_of_cls c117a.2.1 (M := 51840) (by decide)
  have hg := gf FS3.h (fun i hi => FS3.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => FS3.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) FS3.k
  refine .noA6 (not_mem_of_rowK (si (by simp)) rows.2.2.2.2.2.2.1 (prep_si siU.2.1) outS.2.1)
    fun L hLC hL hN => no360_of_five (five_of (si (by simp)) fiveK.1 FS3.h)
      (by rw [hg.1]; decide) (Or.inr (by rw [hC]; decide)) L hLC hL hN

theorem rep117b : RepFacts pi.range l43Model.T.range (pp (K117b.T K117b.r0)) := by
  have hC := card_of_cls c117b.2.1 (M := 51840) (by decide)
  have hg := gf FS4.h (fun i hi => FS4.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => FS4.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) FS4.k
  refine .noA6 (not_mem_of_rowK (si (by simp)) rows.2.2.2.2.2.2.2.1 (prep_si siU.2.1) outS.2.1)
    fun L hLC hL hN => no360_of_five (five_of (si (by simp)) fiveK.2 FS4.h)
      (by rw [hg.1]; decide) (Or.inr (by rw [hC]; decide)) L hLC hL hN

theorem rows_reps : ∀ R ∈ l43Runs, ∀ r ∈ R.rows, ∃ t ∈ l43Reps, ∃ g ∈ pi.range,
    tp 80 r.row.rep = g * t * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, a0, a1, a2, f0, f1, f2, k1080, k10530, k117a, k117b, k8424, -⟩ :=
    binds
  have hc2106 : ∀ {T : Table} {r : ℕ}, bindT T (K2106.T r) = true → r < K2106.N →
      selfInv (K2106.T r) = true → ∃ t ∈ l43Reps, ∃ g ∈ pi.range, tp 80 T = g * t * g⁻¹ := by
    intro T r hb hr hs
    obtain ⟨g, hg, e⟩ := c2106_0.2.2 r hr _ (prep_si hs)
    exact ⟨_, Or.inl rfl, g, hg, (tpR hb hs).trans e⟩
  have hc5265 : ∀ {T : Table} {r : ℕ}, bindT T (K5265.T r) = true → r < K5265.N →
      selfInv (K5265.T r) = true → ∃ t ∈ l43Reps, ∃ g ∈ pi.range, tp 80 T = g * t * g⁻¹ := by
    intro T r hb hr hs
    obtain ⟨g, hg, e⟩ := c5265_0.2.2 r hr _ (prep_si hs)
    exact ⟨_, Or.inr (Or.inl rfl), g, hg, (tpR hb hs).trans e⟩
  have hroot : ∀ {T : Table} {P : ℕ}, bindT T P = true → selfInv P = true → pp P ∈ l43Reps →
      ∃ t ∈ l43Reps, ∃ g ∈ pi.range, tp 80 T = g * t * g⁻¹ := by
    intro T P hb hs hm
    refine ⟨_, hm, 1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact tpR hb hs
  intro R hR r hr
  simp only [l43Runs, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · simp only [runuD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hroot a0 (si (by simp)) (Or.inl rfl)
    · exact hroot k1080 (si (by simp)) (Or.inr (Or.inr (Or.inl rfl)))
    · exact hroot f0 (si (by simp)) (Or.inr (Or.inl rfl))
  · simp only [runuS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hc2106 a1 (by decide) (si (by simp))
    · exact hroot k10530 (si (by simp)) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hc5265 f1 (by decide) (si (by simp))
    · exact hroot k117a (si (by simp)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact hroot k117b (si (by simp)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · simp only [runuDS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc5265 f2 (by decide) (si (by simp))
    · exact hc2106 a2 (by decide) (si (by simp))
    · exact hroot k8424 (si (by simp)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem l43_cover : ∀ τ ∈ l43Model.T.range, orderOf τ = 2 →
    ∃ t ∈ l43Reps, ∃ g ∈ pi.range, τ = g * t * g⁻¹ := by
  rintro _ ⟨α, rfl⟩ hτ2
  have hrow : ∀ R ∈ l43Runs, RunFacts pi.range R →
      l43Model.T α ∈ pi.range ⊔ zpowers (tp 80 R.u) →
      ∃ t ∈ l43Reps, ∃ g ∈ pi.range, l43Model.T α = g * t * g⁻¹ := by
    intro R hR hRF hm
    obtain ⟨r, hr, g, hg, e⟩ := hRF.cover _ hm hτ2
    obtain ⟨t, ht, h, hh, e2⟩ := rows_reps R hR r hr
    refine ⟨t, ht, g * h, mul_mem hg hh, ?_⟩
    rw [e, e2]
    group
  rcases l43_cos α with h | ⟨R, hR, h⟩ | ⟨u, hu, -⟩
  · exact hrow runuD (by simp only [l43Runs, List.mem_cons, true_or]) runFactsD (mem_sup_left h)
  · have hRF := l43_runFacts R hR
    refine hrow R hR hRF ((hRF.memR _).2 (Or.inr ?_))
    have hui : (tp 80 R.u)⁻¹ = tp 80 R.u :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, hRF.u2])
    rwa [hui] at h
  · simp at hu

theorem l43_p1ModelFacts : P1ModelFacts (projectiveSL 4 (ZMod 3)) := by
  refine p1ModelFacts_of_facts l43Model (A₀ := pi.range) rfl (reps := l43Reps) l43_cover ?_
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [rep2106, rep5265, rep1080, rep10530, rep117a, rep117b, rep8424]

end CertificateChecks.KernelP1L43

end
