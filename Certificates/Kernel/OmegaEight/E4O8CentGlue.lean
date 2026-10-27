module

public import Certificates.Kernel.OmegaEight.E4O8CentK
public import Certificates.Kernel.OmegaEight.E4O8NgK
public import Certificates.Kernel.OmegaEight.E4O8NbrGlue
public import CFSG.Certificates.Kernel.PCentCheck
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E4C

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.KC.PCent CFSG.KC.Misc.ArrEnum CertificateChecks.KernelO8 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4O8

theorem ch550106sq : bAnd(Nat.beq (pc e4U e4U) (mainK 0), bAnd(Nat.beq (pc (mainK 0) (mainK 0)) pid,
    bIf(Nat.beq (mainK 0) pid, false, true))) = true := by
  quickRfl

theorem e4c_pp {p : Nat} (h : permB 360 9 p = true) : CFSG.KC.BfsPin.PP 360 9 p :=
  pp_of_permB ch550106sz h

theorem e4c_toPerm {p : Nat} (h : permB 360 9 p = true) :
    toPerm 360 9 p = permOfArr 360 (unpack 360 9 p) := by
  have hpm : pm p = true := h
  have hr := (rep_permOfArr (isInvA_of hpm)).1
  refine Equiv.ext fun i => Fin.ext ?_
  rw [toPerm_apply (e4c_pp h), ← hr i, at9_eq i.2]
  rfl

theorem e4c_omegaT : Subgroup.closure (gens 360 9 AP.S 8) = omegaT := by
  rw [omegaT_eq]; congr 1; ext g; constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [gen, gen_get (by omega), e4c_toPerm (root_facts hk).2.2.1]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [gen, gen_get (by omega), e4c_toPerm (root_facts hk).2.2.1]⟩

theorem e4c_mul {p q : Nat} (hp : CFSG.KC.BfsPin.PP 360 9 p) (hq : CFSG.KC.BfsPin.PP 360 9 q) :
    toPerm 360 9 (pc p q) = toPerm 360 9 p * toPerm 360 9 q :=
  toPerm_mul hp hq

theorem e4c_comm {a b : Nat} (ha : CFSG.KC.BfsPin.PP 360 9 a) (hb : CFSG.KC.BfsPin.PP 360 9 b)
    (h : Nat.beq (pc a b) (pc b a) = true) :
    toPerm 360 9 a * toPerm 360 9 b = toPerm 360 9 b * toPerm 360 9 a := by
  rw [← e4c_mul ha hb, ← e4c_mul hb ha, Nat.eq_of_beq_eq_true h]

theorem e4c_pid : toPerm 360 9 pid = 1 := toPerm_pidn ch550106sz

theorem e4c_lets {k : Nat} {W : List (List Nat)} (h : e4Lets k W = true) (j : Nat) :
    ∀ c ∈ W.getD j [], c < k := by
  intro c hc
  unfold e4Lets at h
  by_cases hj : j < W.length
  · rw [List.getD_eq_getElem _ _ hj] at hc
    have e := allL_iff.1 (List.all_eq_true.1 h _ (List.getElem_mem hj)) c hc
    rwa [Nat.blt_eq] at e
  · rw [List.getD_eq_default _ _ (by omega)] at hc
    exact absurd hc List.not_mem_nil

theorem e4c_closure_le {G : Nat → Nat} {ngen : Nat} {K : Subgroup (Equiv.Perm (Fin 360))}
    (h : ∀ k < ngen, toPerm 360 9 (G k) ∈ K) : Subgroup.closure (gens 360 9 G ngen) ≤ K := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact h k hk

theorem e4c_mem_cent {a v : Equiv.Perm (Fin 360)} (h : a * v = v * a) :
    a ∈ Subgroup.centralizer {v} :=
  Subgroup.mem_centralizer_singleton_iff.2 h

theorem e4c_step {A B : Subgroup (Equiv.Perm (Fin 360))} {v : Equiv.Perm (Fin 360)} {m M : Nat}
    (hle : B ≤ A ⊓ Subgroup.centralizer {v})
    (hm : m * Nat.card (A ⊓ Subgroup.centralizer {v} : Subgroup (Equiv.Perm (Fin 360))) ≤
      Nat.card A)
    (hA : Nat.card A = m * M) (hB : M ≤ Nat.card B) (hm0 : 0 < m) :
    B = A ⊓ Subgroup.centralizer {v} ∧ Nat.card B = M := by
  have h1 : Nat.card (A ⊓ Subgroup.centralizer {v} : Subgroup (Equiv.Perm (Fin 360))) ≤ M := by
    rw [hA] at hm
    exact Nat.le_of_mul_le_mul_left hm hm0
  have h2 := Subgroup.card_le_of_le hle
  exact ⟨Subgroup.eq_of_le_of_card_ge hle (by omega), by omega⟩

theorem e4c_card_le {K : Subgroup (Equiv.Perm (Fin 360))} (S : Finset (Equiv.Perm (Fin 360)))
    (h : ∀ s ∈ S, s ∈ K) : S.card ≤ Nat.card K := by
  have := Nat.card_le_card_of_injective (fun s : S => (⟨s.1, h _ s.2⟩ : K))
    (fun a b e => by
      have e' := congrArg Subtype.val e
      exact Subtype.ext e')
  rwa [Nat.card_eq_finsetCard] at this

theorem e4c_reach_left {G : Nat → Nat} {ngen : Nat}
    (hG : ∀ k < ngen, CFSG.KC.BfsPin.PP 360 9 (G k)) {y : Nat}
    (h : Reach (fun k y => pcomp 360 9 (mask 9) (G k) y) ngen pid y) :
    CFSG.KC.BfsPin.PP 360 9 y ∧ toPerm 360 9 y ∈ Subgroup.closure (gens 360 9 G ngen) := by
  induction h with
  | root => exact ⟨CFSG.KC.BfsPin.PP.id ch550106sz, by rw [e4c_pid]; exact Subgroup.one_mem _⟩
  | step k hk _ ih =>
    exact ⟨(hG k hk).mul ih.1, by
      rw [toPerm_mul (hG k hk) ih.1]
      exact Subgroup.mul_mem _ (gen_mem hk) ih.2⟩

theorem e4c_pm : (∀ k < 6, CFSG.KC.BfsPin.PP 360 9 (g0K k)) ∧
    (∀ k < 6, CFSG.KC.BfsPin.PP 360 9 (g1K k)) ∧ (∀ k < 6, CFSG.KC.BfsPin.PP 360 9 (g2K k)) ∧
    (∀ k < 4, CFSG.KC.BfsPin.PP 360 9 (g3K k)) ∧ CFSG.KC.BfsPin.PP 360 9 C ∧
    CFSG.KC.BfsPin.PP 360 9 (mainK 0) ∧ CFSG.KC.BfsPin.PP 360 9 e4U ∧
    CFSG.KC.BfsPin.PP 360 9 om0V := by
  have h := ch550106pm
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2, h3, hc, hx, hu, hv⟩ := h
  exact ⟨fun k hk => e4c_pp (allN_spec h0 k hk), fun k hk => e4c_pp (allN_spec h1 k hk),
    fun k hk => e4c_pp (allN_spec h2 k hk), fun k hk => e4c_pp (allN_spec h3 k hk), e4c_pp hc,
    e4c_pp hx, e4c_pp hu, e4c_pp hv⟩

theorem e4c_x0 : toPerm 360 9 (mainK 0) = mainPerm 0 := by
  obtain ⟨e, -, p⟩ := main_ok (by norm_num : 0 < 5)
  rw [mainPerm, e, e4c_toPerm p]

theorem e4c_u0 : toPerm 360 9 e4U = permOfArr 360 (u0A ()) := by
  have h := ch550106pm
  simp only [bAnd_iff] at h
  rw [u0A_pk, e4c_toPerm h.2.2.2.2.2.2.1]

theorem e4c_v0 : toPerm 360 9 om0V = permOfArr 360 (v0A ()) := by
  have h := ch550106pm
  simp only [bAnd_iff] at h
  rw [v0A_pk, e4c_toPerm h.2.2.2.2.2.2.2]

theorem e4c_x0_facts : toPerm 360 9 e4U * toPerm 360 9 e4U = toPerm 360 9 (mainK 0) ∧
    toPerm 360 9 (mainK 0) * toPerm 360 9 (mainK 0) = 1 ∧ toPerm 360 9 (mainK 0) ≠ 1 := by
  obtain ⟨-, -, -, -, -, hpx, hpu, -⟩ := e4c_pm
  have h := ch550106sq
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [← e4c_mul hpu hpu, Nat.eq_of_beq_eq_true h1],
    by rw [← e4c_mul hpx hpx, Nat.eq_of_beq_eq_true h2, e4c_pid], fun e => ?_⟩
  have e' : mainK 0 = pid :=
    toPerm_injective hpx (CFSG.KC.BfsPin.PP.id ch550106sz) (by rw [e, e4c_pid])
  rw [e', Nat.beq_refl] at h3
  exact Bool.noConfusion h3

theorem e4c_u0_sq : toPerm 360 9 e4U * toPerm 360 9 e4U = toPerm 360 9 (mainK 0) :=
  e4c_x0_facts.1

theorem e4c_word_mem {w : List Int} (hk : lettersK 17 w = true)
    (ho : CFSG.Monster.B.Co2.Native.lettersOK 17 w = true) (hp : permB 360 9 (wO w) = true) :
    toPerm 360 9 (wO w) ∈ omegaT := by
  rw [e4c_toPerm hp, ← omegaW_eq hk]
  exact (omegaW_spec ho).2

@[expose] noncomputable def e4H0 : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure (gens 360 9 g0K 6)

@[expose] noncomputable def e4H1 : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure (gens 360 9 g1K 6)

@[expose] noncomputable def e4H2 : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure (gens 360 9 g2K 6)

theorem e4c_G0_mem {k : Nat} (hk : k < 6) :
    toPerm 360 9 (g0K k) ∈ omegaT := by
  have hg := ch550106g0
  simp only [bAnd_iff] at hg
  obtain ⟨e0, e1, e2, -, -⟩ := hg
  have hpm := e4c_pm.1
  have hu0 := ch550106u
  simp only [bAnd_iff] at hu0
  have hu := hu0.1
  unfold classK at hu
  rw [Bool.and_eq_true] at hu
  have hinv : ∀ j < 3, g0K (j + 3) = pinvS 360 9 (mask 9) (g0K j) := by
    intro j hj
    have e := Nat.eq_of_beq_eq_true (allN_spec hu.1 j (by omega))
    have hm : Nat.mod (Nat.add j (nat_lit 3)) (nat_lit 6) = j + 3 := by
      change (j + 3) % 6 = j + 3
      omega
    have e' : gi0K j = g0K (j + 3) := congrArg g0K hm
    rw [← e', e]
  have h3 : ∀ j < 3, toPerm 360 9 (g0K j) ∈ omegaT := by
    intro j hj
    have hpj : permB 360 9 (g0K j) = true := permB_of_pp (hpm j (by omega))
    interval_cases j
    · rw [Nat.eq_of_beq_eq_true e0] at hpj ⊢
      exact e4c_word_mem (by decide +kernel) (by decide +kernel) hpj
    · rw [Nat.eq_of_beq_eq_true e1] at hpj ⊢
      exact e4c_word_mem (by decide +kernel) (by decide +kernel) hpj
    · rw [Nat.eq_of_beq_eq_true e2] at hpj ⊢
      exact e4c_word_mem (by decide +kernel) (by decide +kernel) hpj
  by_cases hk3 : k < 3
  · exact h3 k hk3
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    rw [hinv j (by omega), toPerm_inv (hpm j (by omega))]
    exact omegaT.inv_mem (h3 j (by omega))

theorem e4c_H0 :
    e4H0 = omegaT ⊓ Subgroup.centralizer {mainPerm 0} ∧ Nat.card e4H0 = 110592 := by
  obtain ⟨hp0, -, -, -, -, hpx, -, -⟩ := e4c_pm
  have hx := ch550106x
  simp only [bAnd_iff] at hx
  have hb := card_centralizer_le_of_classK (fun k hk => e4c_pp (root_facts hk).2.2.1) hpx hx.1
  rw [e4c_omegaT, e4c_x0, Nat.eq_of_beq_eq_true hx.2, card_omegaT] at hb
  have hg := ch550106g0
  simp only [bAnd_iff] at hg
  have hl := ch550106l0
  simp only [bAnd_iff] at hl
  have hlow := prod_le_card_of_stabLowK ch550106sz hp0 hl.1
  rw [Nat.eq_of_beq_eq_true hl.2] at hlow
  refine e4c_step (m := 1575) (e4c_closure_le fun k hk => Subgroup.mem_inf.2
    ⟨e4c_G0_mem hk, e4c_mem_cent ?_⟩) (by rw [card_omegaT]; exact hb) card_omegaT hlow
    (by norm_num)
  rw [← e4c_x0]
  exact e4c_comm (hp0 k hk) hpx (allN_spec hg.2.2.2.2 k hk)

theorem e4c_H1 :
    e4H1 = e4H0 ⊓ Subgroup.centralizer {toPerm 360 9 e4U} ∧ Nat.card e4H1 = 4608 := by
  obtain ⟨hp0, hp1, -, -, -, -, hpu, -⟩ := e4c_pm
  have hcu := ch550106u
  simp only [bAnd_iff] at hcu
  have hc := card_centralizer_le_of_classK hp0 hpu hcu.1
  rw [Nat.eq_of_beq_eq_true hcu.2] at hc
  have hg := ch550106g1
  simp only [bAnd_iff] at hg
  obtain ⟨-, -, hlet, hw⟩ := hg
  have hl := ch550106l1
  simp only [bAnd_iff] at hl
  have hlow := prod_le_card_of_stabLowK ch550106sz hp1 hl.1
  rw [Nat.eq_of_beq_eq_true hl.2] at hlow
  refine e4c_step (m := 24) (e4c_closure_le fun k hk => ?_) hc
    (by rw [e4c_H0.2]) hlow (by norm_num)
  have e := allN_spec hw k hk
  simp only [bAnd_iff] at e
  refine Subgroup.mem_inf.2 ⟨?_, e4c_mem_cent (e4c_comm (hp1 k hk) hpu e.2)⟩
  rw [Nat.eq_of_beq_eq_true e.1]
  exact (wordK_sound ch550106sz hp0 _ (e4c_lets hlet k)).2

theorem e4c_H2 :
    e4H2 = e4H1 ⊓ Subgroup.centralizer {toPerm 360 9 om0V} ∧ Nat.card e4H2 = 1152 := by
  obtain ⟨-, hp1, hp2, -, -, -, hpu, hpv⟩ := e4c_pm
  have hcv := ch550106v
  simp only [bAnd_iff] at hcv
  have hc := card_centralizer_le_of_classK hp1 hpv hcv.1
  rw [Nat.eq_of_beq_eq_true hcv.2] at hc
  have hg := ch550106g2
  simp only [bAnd_iff] at hg
  obtain ⟨-, -, hlet, hw⟩ := hg
  have hl := ch550106l2
  simp only [bAnd_iff] at hl
  have hlow := prod_le_card_of_stabLowK ch550106sz hp2 hl.1
  rw [Nat.eq_of_beq_eq_true hl.2] at hlow
  refine e4c_step (m := 4) (e4c_closure_le fun k hk => ?_) hc
    (by rw [e4c_H1.2]) hlow (by norm_num)
  have e := allN_spec hw k hk
  simp only [bAnd_iff] at e
  refine Subgroup.mem_inf.2 ⟨?_, e4c_mem_cent (e4c_comm (hp2 k hk) hpv e.2.2)⟩
  rw [Nat.eq_of_beq_eq_true e.1]
  exact (wordK_sound ch550106sz hp1 _ (e4c_lets hlet k)).2

theorem e4c_mem_H2 {a : Equiv.Perm (Fin 360)} (ha : a ∈ omegaT)
    (hu : a * toPerm 360 9 e4U = toPerm 360 9 e4U * a)
    (hv : a * toPerm 360 9 om0V = toPerm 360 9 om0V * a) : a ∈ e4H2 := by
  have hx : a * mainPerm 0 = mainPerm 0 * a := by
    rw [← e4c_x0, ← e4c_u0_sq, ← mul_assoc, hu, mul_assoc, hu, mul_assoc]
  rw [e4c_H2.1, e4c_H1.1, e4c_H0.1]
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨ha, e4c_mem_cent hx⟩,
    e4c_mem_cent hu⟩, e4c_mem_cent hv⟩

theorem e4c_C :
    toPerm 360 9 C ∈ e4H0 ∧ toPerm 360 9 C ^ 3 = 1 := by
  obtain ⟨hp0, -, -, -, hpc, -, -, -⟩ := e4c_pm
  have h := ch550106c
  simp only [bAnd_iff] at h
  obtain ⟨e, hlet, h3, -, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Nat.eq_of_beq_eq_true e]
    exact (wordK_sound ch550106sz hp0 _ (e4c_lets hlet 0)).2
  · rw [pow_three, ← e4c_mul hpc hpc, ← e4c_mul (q := pc C C) hpc (hpc.mul hpc),
      Nat.eq_of_beq_eq_true h3,
      e4c_pid]

theorem e4c_move : ∀ a ∈ omegaT, a * a = 1 → a ≠ 1 →
    a ≠ mainPerm 0 → a * permOfArr 360 (u0A ()) = permOfArr 360 (u0A ()) * a →
    a * permOfArr 360 (v0A ()) = permOfArr 360 (v0A ()) * a →
    ∃ c ∈ omegaT, c ^ 3 = 1 ∧ c * mainPerm 0 = mainPerm 0 * c ∧ c * a ≠ a * c := by
  classical
  intro a ha ha2 ha1 hax hau hav
  rw [← e4c_u0] at hau
  rw [← e4c_v0] at hav
  obtain ⟨-, -, hp2, hp3, hpc, hpx, -, -⟩ := e4c_pm
  have haH := e4c_mem_H2 ha hau hav
  obtain ⟨hcH, hc3⟩ := e4c_C
  rw [e4c_H0.1] at hcH
  obtain ⟨hcΩ, hcx⟩ := Subgroup.mem_inf.1 hcH
  refine ⟨toPerm 360 9 C, hcΩ, hc3, Subgroup.mem_centralizer_singleton_iff.1 hcx, fun hca => ?_⟩
  have hcc := ch550106c
  simp only [bAnd_iff] at hcc
  obtain ⟨-, -, -, hcls, hclen⟩ := hcc
  have hb := card_centralizer_le_of_classK hp2 hpc hcls
  rw [Nat.eq_of_beq_eq_true hclen] at hb
  change 64 * Nat.card (e4H2 ⊓ Subgroup.centralizer {toPerm 360 9 C} :
    Subgroup (Equiv.Perm (Fin 360))) ≤ Nat.card e4H2 at hb
  rw [e4c_H2.2] at hb
  have hg := ch550106g3
  simp only [bAnd_iff] at hg
  obtain ⟨-, -, hlet, hw, hR, hlen⟩ := hg
  have hG3 : Subgroup.closure (gens 360 9 g3K 4) ≤
      e4H2 ⊓ Subgroup.centralizer {toPerm 360 9 C} := e4c_closure_le fun k hk => by
    have e := allN_spec hw k hk
    simp only [bAnd_iff] at e
    refine Subgroup.mem_inf.2 ⟨?_, e4c_mem_cent (e4c_comm (hp3 k hk) hpc e.2)⟩
    rw [Nat.eq_of_beq_eq_true e.1]
    exact (wordK_sound ch550106sz hp2 _ (e4c_lets hlet k)).2
  obtain ⟨hs, hr⟩ := orbRecK_sound hR
  have hval : ∀ x ∈ R3.map Prod.fst, CFSG.KC.BfsPin.PP 360 9 x ∧
      toPerm 360 9 x ∈ e4H2 ⊓ Subgroup.centralizer {toPerm 360 9 C} := by
    intro x hx
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2⟩ := e4c_reach_left hp3 (hr r hr')
    exact ⟨h1, hG3 h2⟩
  set S : Finset (Equiv.Perm (Fin 360)) := ((R3.map Prod.fst).map (toPerm 360 9)).toFinset
  have hS : S.card = 18 := by
    rw [List.toFinset_card_of_nodup, List.length_map, List.length_map,
      Nat.eq_of_beq_eq_true hlen]
    refine List.Nodup.map_on (fun x hx y hy e => ?_) (hs.imp (fun h => Nat.ne_of_lt h))
    exact toPerm_injective (hval x hx).1 (hval y hy).1 e
  have haC : a ∈ e4H2 ⊓ Subgroup.centralizer {toPerm 360 9 C} :=
    Subgroup.mem_inf.2 ⟨haH, e4c_mem_cent hca.symm⟩
  have haS : a ∈ S := by
    by_contra haS
    have h19 := e4c_card_le (K := e4H2 ⊓ Subgroup.centralizer {toPerm 360 9 C}) (insert a S)
      (fun s hs' => by
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact haC
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs')
          exact (hval x hx).2)
    rw [Finset.card_insert_of_notMem haS, hS] at h19
    omega
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 haS)
  have hpr := (hval r hr').1
  have hrr : pc r r = pid := toPerm_injective (hpr.mul hpr) (CFSG.KC.BfsPin.PP.id ch550106sz)
    (by rw [e4c_mul hpr hpr, ha2, e4c_pid])
  have hi := allL_iff.1 ch550106i r hr'
  rw [hrr, Nat.beq_refl] at hi
  change (bIf(Nat.beq r pid, true, Nat.beq r (mainK 0))) = true at hi
  cases e : Nat.beq r pid
  · rw [e] at hi
    exact hax (by rw [Nat.eq_of_beq_eq_true hi, e4c_x0])
  · exact ha1 (by rw [Nat.eq_of_beq_eq_true e, e4c_pid])

@[expose] noncomputable def e4H4 : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure (gens 360 9 g4K 6)

theorem e4c_ng_pm : (∀ k < 6, CFSG.KC.BfsPin.PP 360 9 (g4K k)) ∧ CFSG.KC.BfsPin.PP 360 9 Y1 ∧
    CFSG.KC.BfsPin.PP 360 9 Y2 := by
  have h := ch55116pm
  simp only [bAnd_iff] at h
  exact ⟨fun k hk => e4c_pp (allN_spec h.1 k hk), e4c_pp h.2.1, e4c_pp h.2.2⟩

theorem e4c_ys : ∀ y ∈ [Y1, Y2], toPerm 360 9 y ∈ omegaT ∧
    toPerm 360 9 y ^ 3 = 1 ∧ toPerm 360 9 y * toPerm 360 9 e4U = toPerm 360 9 e4U * toPerm 360 9 y ∧
    toPerm 360 9 y * toPerm 360 9 om0V = toPerm 360 9 om0V * toPerm 360 9 y := by
  obtain ⟨-, -, -, -, -, -, hpu, hpv⟩ := e4c_pm
  obtain ⟨-, hp1, hp2⟩ := e4c_ng_pm
  have h := ch55116y
  simp only [bAnd_iff] at h
  obtain ⟨l1, l2, e1, e2, c1, c2, u1, v1, u2, v2⟩ := h
  have key : ∀ {y : Nat} {w : List Int}, CFSG.KC.BfsPin.PP 360 9 y → lettersK 17 w = true →
      CFSG.Monster.B.Co2.Native.lettersOK 17 w = true → Nat.beq y (wO w) = true →
      Nat.beq (pc y (pc y y)) pid = true → Nat.beq (pc y e4U) (pc e4U y) = true →
      Nat.beq (pc y om0V) (pc om0V y) = true → toPerm 360 9 y ∈ omegaT ∧
      toPerm 360 9 y ^ 3 = 1 ∧
      toPerm 360 9 y * toPerm 360 9 e4U = toPerm 360 9 e4U * toPerm 360 9 y ∧
      toPerm 360 9 y * toPerm 360 9 om0V = toPerm 360 9 om0V * toPerm 360 9 y := by
    intro y w hp hk ho he h3 hu hv
    refine ⟨?_, ?_, e4c_comm hp hpu hu, e4c_comm hp hpv hv⟩
    · have hpw : permB 360 9 (wO w) = true := by
        rw [← Nat.eq_of_beq_eq_true he]
        exact permB_of_pp hp
      rw [Nat.eq_of_beq_eq_true he]
      exact e4c_word_mem hk ho hpw
    · rw [pow_three, ← e4c_mul hp hp, ← e4c_mul (q := pc y y) hp (hp.mul hp),
        Nat.eq_of_beq_eq_true h3,
        e4c_pid]
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact key hp1 l1 (by decide +kernel) e1 c1 u1 v1
  · exact key hp2 l2 (by decide +kernel) e2 c2 u2 v2

theorem e4c_noGood : ∀ x ∈ omegaT,
    x * mainPerm 0 = mainPerm 0 * x → (∃ k : ℕ, x ^ 3 ^ k = 1) → x ≠ 1 →
    ∃ y ∈ omegaT, y ^ 3 = 1 ∧ y * permOfArr 360 (u0A ()) = permOfArr 360 (u0A ()) * y ∧
      y * permOfArr 360 (v0A ()) = permOfArr 360 (v0A ()) * y ∧ x * y ≠ y * x := by
  intro x hx hxx ⟨k, hk⟩ hx1
  rw [← e4c_u0, ← e4c_v0]
  obtain ⟨hp0, -, -, -, -, hpx, hpu, -⟩ := e4c_pm
  obtain ⟨hp4, hp1, hp2⟩ := e4c_ng_pm
  by_contra hno
  have hy1 := e4c_ys Y1 (by simp)
  have hy2 := e4c_ys Y2 (by simp)
  have hc1 : x * toPerm 360 9 Y1 = toPerm 360 9 Y1 * x := by_contra fun h =>
    hno ⟨_, hy1.1, hy1.2.1, hy1.2.2.1, hy1.2.2.2, h⟩
  have hc2 : x * toPerm 360 9 Y2 = toPerm 360 9 Y2 * x := by_contra fun h =>
    hno ⟨_, hy2.1, hy2.2.1, hy2.2.2.1, hy2.2.2.2, h⟩
  have hcy1 := ch55116c1
  simp only [bAnd_iff] at hcy1
  have hb1 := card_centralizer_le_of_classK hp0 hp1 hcy1.1
  rw [Nat.eq_of_beq_eq_true hcy1.2] at hb1
  have hg := ch55116g4
  simp only [bAnd_iff] at hg
  obtain ⟨-, -, hlet, hw⟩ := hg
  have hlet' : e4Lets 6 W4 = true := hlet
  have hl := ch55116l4
  simp only [bAnd_iff] at hl
  have hlow := prod_le_card_of_stabLowK ch550106sz hp4 hl.1
  rw [Nat.eq_of_beq_eq_true hl.2] at hlow
  obtain ⟨hH4, hc4⟩ := e4c_step (B := e4H4) (m := 512) (M := 216)
    (e4c_closure_le fun k hk => by
      have e := allN_spec hw k hk
      simp only [bAnd_iff] at e
      refine Subgroup.mem_inf.2 ⟨?_, e4c_mem_cent (e4c_comm (hp4 k hk) hp1 e.2)⟩
      rw [Nat.eq_of_beq_eq_true e.1]
      exact (wordK_sound ch550106sz hp0 _ (e4c_lets hlet' k)).2) hb1
    (by change Nat.card e4H0 = _; rw [e4c_H0.2]) hlow (by norm_num)
  have hcy2 := ch55116c2
  simp only [bAnd_iff] at hcy2
  have hb2 := card_centralizer_le_of_classK hp4 hp2 hcy2.1
  rw [Nat.eq_of_beq_eq_true hcy2.2] at hb2
  change 27 * Nat.card (e4H4 ⊓ Subgroup.centralizer {toPerm 360 9 Y2} :
    Subgroup (Equiv.Perm (Fin 360))) ≤ Nat.card e4H4 at hb2
  rw [hc4] at hb2
  set H : Subgroup (Equiv.Perm (Fin 360)) := e4H4 ⊓ Subgroup.centralizer {toPerm 360 9 Y2}
  have hH8 : Nat.card H ≤ 8 := by omega
  have hmem : ∀ g ∈ omegaT, g * mainPerm 0 = mainPerm 0 * g →
      g * toPerm 360 9 Y1 = toPerm 360 9 Y1 * g → g * toPerm 360 9 Y2 = toPerm 360 9 Y2 * g →
      g ∈ H := by
    intro g hg hgx hg1 hg2
    refine Subgroup.mem_inf.2 ⟨?_, e4c_mem_cent hg2⟩
    rw [hH4]
    change g ∈ e4H0 ⊓ _
    rw [e4c_H0.1]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg, e4c_mem_cent hgx⟩, e4c_mem_cent hg1⟩
  have hxH := hmem x hx hxx hc1 hc2
  obtain ⟨hsq, hx2, hx0⟩ := e4c_x0_facts
  have huΩ : toPerm 360 9 e4U ∈ omegaT := by
    rw [e4c_u0]
    exact (omegaW_spec (w := CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 CFSG.ClassicalInvolution.Q3.TL4.E4O8Data.u0Word)
      (by decide +kernel)).2
  have huH : toPerm 360 9 e4U ∈ H := hmem _ huΩ
    (by rw [← e4c_x0, ← hsq, mul_assoc]) hy1.2.2.1.symm hy2.2.2.1.symm
  have hu4 : orderOf (toPerm 360 9 e4U) = 2 ^ (1 + 1) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, pow_two, hsq]
      exact hx0
    · have e : (2 : ℕ) ^ (1 + 1) = 2 * 2 := rfl
      rw [e, pow_mul, pow_two (toPerm 360 9 e4U ^ 2), pow_two (toPerm 360 9 e4U), hsq, hx2]
  have h4 : 4 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H huH
    rwa [hu4] at this
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h8 : Nat.card H ∣ 8 := by
    rcases (by omega : Nat.card H = 4 ∨ Nat.card H = 8) with e | e <;> rw [e] <;> norm_num
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
  have h38 : 3 ^ j ∣ 8 := hj ▸ (Subgroup.orderOf_dvd_natCard H hxH).trans h8
  have hj0 : j = 0 := by
    by_contra hj0
    have : 3 ∣ 8 := (dvd_pow_self 3 hj0).trans h38
    omega
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact hx1 hj

end CertificateChecks.KernelO8.E4C

end
