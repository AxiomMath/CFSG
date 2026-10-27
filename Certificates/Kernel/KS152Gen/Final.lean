module

public import Certificates.Kernel.KS152Gen.Checks
public import CFSG.Certificates.Kernel.KS152GenSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2Sound
public import Certificates.Kernel.J2Cover.AutChain
public import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.KS152Gen

open Subgroup CFSG.KD.J2Five CFSG.KC.Enum CFSG.KS CFSG.ComponentClassification.J2Cover
  CFSG.RankThree.PartTwo.KFacts.KS152J2

noncomputable def σ0 (i : ℕ) : Equiv.Perm (Fin 315) :=
  [CFSG.Monster.B.Co2.permOfArr 315 autStrong[0]!, CFSG.Monster.B.Co2.permOfArr 315 autStrong[1]!,
    (CFSG.Monster.B.Co2.permOfArr 315 autStrong[1]!)⁻¹].getD i 1

theorem g00_eq : getN g0 0 = CertificateChecks.KernelJ2Cover.PA.S 0 := by decide +kernel

theorem g01_eq : getN g0 1 = CertificateChecks.KernelJ2Cover.PA.S 1 := by decide +kernel

theorem prep_of_arr {p : ℕ} {g : Equiv.Perm (Fin 315)}
    (h : CFSG.Monster.B.Co2.Rep 315 (CFSG.KS.Raw.unpack 315 9 p) g) : PRep p g := by
  intro q hq
  have e := h ⟨q, hq⟩
  rw [CFSG.KC.BfsPin.unpack_get' hq] at e
  exact e

theorem hpts : ∀ p ∈ pts, p < 315 := by
  intro p hp
  simp only [pts, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega


theorem prep_a : PRep (getN g0 0) (CFSG.Monster.B.Co2.permOfArr 315 autStrong[0]!) := by
  have ha : autStrong[0]! = CFSG.KS.Raw.unpack 315 9 (CertificateChecks.KernelJ2Cover.PA.S 0) :=
    CertificateChecks.KernelJ2Cover.binds.2.2.2.2.1 0 (by norm_num)
  have h : CFSG.Monster.B.Co2.Rep 315 autStrong[0]!
      (CFSG.Monster.B.Co2.permOfArr 315 autStrong[0]!) := rep_permA
  rw [ha] at h
  rw [g00_eq]
  have := prep_of_arr h
  rwa [← ha] at this

theorem prep_b : PRep (getN g0 1) (CFSG.Monster.B.Co2.permOfArr 315 autStrong[1]!) := by
  have hb : autStrong[1]! = CFSG.KS.Raw.unpack 315 9 (CertificateChecks.KernelJ2Cover.PA.S 1) :=
    CertificateChecks.KernelJ2Cover.binds.2.2.2.2.1 1 (by norm_num)
  have h : CFSG.Monster.B.Co2.Rep 315 autStrong[1]!
      (CFSG.Monster.B.Co2.permOfArr 315 autStrong[1]!) := rep_permB
  rw [hb] at h
  rw [g01_eq]
  have := prep_of_arr h
  rwa [← hb] at this

theorem hG0 : ∀ i < g0.length, PRep (getN g0 i) (σ0 i) := by
  have h := base_ok
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h
  obtain ⟨hl, e2, e3⟩ := h
  intro i hi
  rw [hl] at hi
  have pb := prep_b
  interval_cases i
  · exact prep_a
  · exact pb
  · have h1 := (prep_eq (prep_pm pb (prep_pm pb pb)) prep_one).1 e3
    have h2 : CFSG.Monster.B.Co2.permOfArr 315 autStrong[1]! *
        CFSG.Monster.B.Co2.permOfArr 315 autStrong[1]! =
        (CFSG.Monster.B.Co2.permOfArr 315 autStrong[1]!)⁻¹ :=
      (inv_eq_of_mul_eq_one_right h1).symm
    have := prep_of_eq e2 (prep_pm pb pb)
    rw [h2] at this
    exact this

theorem g0_len : g0.length = 3 := by
  have h := base_ok
  rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h
  exact h.1

theorem σ0_mem : ∀ i < g0.length, σ0 i ∈ genGroup 315 autStrong[0]! autStrong[1]! := by
  intro i hi
  rw [g0_len] at hi
  interval_cases i
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact inv_mem (subset_closure (Set.mem_insert_of_mem _ rfl))

theorem vals {E : List ℕ} {Ws : List (List ℕ)} (h : valsOK g0 E Ws = true) :
    E.length = Ws.length ∧ ∀ i < E.length, PRep (getN E i) (wordP σ0 (Ws.getD i [])) ∧
      wordP σ0 (Ws.getD i []) ∈ genGroup 315 autStrong[0]! autStrong[1]! := by
  obtain ⟨hl, h⟩ := valsOK_sound hG0 h
  exact ⟨hl, fun i hi => ⟨(h i hi).2, wordP_mem _ σ0_mem (h i hi).1⟩⟩

theorem cent_ge {X : Subgroup (Equiv.Perm (Fin 315))} {y : Equiv.Perm (Fin 315)}
    {A K T : Subgroup (Equiv.Perm (Fin 315))} (hA : A ≤ X ⊓ centralizer {y})
    (hK : K ≤ X ⊓ centralizer {y}) (hT : T ≤ X ⊓ centralizer {y}) (hA' : Nat.card A = 25)
    (hK' : Nat.card K = 4) (hT' : Nat.card T = 3) : 300 ≤ Nat.card ↥(X ⊓ centralizer {y}) := by
  have d1 := Subgroup.card_dvd_of_le hA
  have d2 := Subgroup.card_dvd_of_le hK
  have d3 := Subgroup.card_dvd_of_le hT
  rw [hA'] at d1
  rw [hK'] at d2
  rw [hT'] at d3
  have d12 : 25 * 4 ∣ Nat.card ↥(X ⊓ centralizer {y}) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
  have d : 25 * 4 * 3 ∣ Nat.card ↥(X ⊓ centralizer {y}) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d12 d3
  exact Nat.le_of_dvd Nat.card_pos d

theorem mem_cent_of {x y : Equiv.Perm (Fin 315)} (h : x * y = y * x) : x ∈ centralizer {y} :=
  mem_centralizer_singleton_iff.2 h

theorem comm_sound {x y : ℕ} {X Y : Equiv.Perm (Fin 315)} (hx : PRep x X) (hy : PRep y Y)
    (h : comm x y = true) : X * Y = Y * X :=
  (prep_eq (prep_pm hx hy) (prep_pm hy hx)).1 h

theorem ne_one_sound {x : ℕ} {X : Equiv.Perm (Fin 315)} (hx : PRep x X)
    (h : Bool.rec (motive := fun _ => Bool) true false (eq x one) = true) : X ≠ 1 := by
  rw [bIf_eq, Bool.not_eq_true'] at h
  intro e
  rw [(prep_eq hx prep_one).2 e] at h
  exact absurd h (by decide)

theorem facts : ∃ (Tp Wp Sp : Subgroup (Equiv.Perm (Fin 315))) (z0 y0 : Equiv.Perm (Fin 315)),
    Tp ≤ genGroup 315 autStrong[0]! autStrong[1]! ∧ Nat.card Tp = 128 ∧
      Wp ≤ genGroup 315 autStrong[0]! autStrong[1]! ∧
      Wp ≤ Subgroup.closure ((fun x : Equiv.Perm (Fin 315) => x ^ 2) '' (Tp : Set _)) ∧
      Sp ≤ genGroup 315 autStrong[0]! autStrong[1]! ∧ Nat.card Sp = 27 ∧ z0 ≠ 1 ∧ z0 ∈ Sp ∧
      Sp ≤ Subgroup.centralizer ({z0} : Set (Equiv.Perm (Fin 315))) ∧
      y0 ∈ genGroup 315 autStrong[0]! autStrong[1]! ∧ y0 ^ 5 = 1 ∧ y0 ≠ 1 ∧ z0 * y0 = y0 * z0 ∧
      ∀ g ∈ genGroup 315 autStrong[0]! autStrong[1]!,
        genGroup 315 autStrong[0]! autStrong[1]! ≤ Wp ⊔ Subgroup.zpowers (g * y0 * g⁻¹) := by
  set X := genGroup 315 autStrong[0]! autStrong[1]! with hXdef
  have hXc : Nat.card X = 604800 := card_P
  obtain ⟨-, hY⟩ := vals vals_y
  obtain ⟨pY, mY⟩ := hY 0 (by norm_num)
  set Y := wordP σ0 ([yw].getD 0 []) with hYdef
  change PRep yg Y at pY
  obtain ⟨hTl, hT⟩ := vals vals_t
  have ht := t_ok
  unfold ckT at ht
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at ht
  simp only [Bool.and_eq_true, Nat.beq_eq, lenW_eq, lenN_eq] at ht
  obtain ⟨hTg, h128, hx4, hq4, hxs⟩ := ht
  set Tg : ℕ → Equiv.Perm (Fin 315) := fun k => wordP σ0 (tw.getD k [])
  obtain ⟨hTmem, hTcard, -, hTrep, -, -⟩ :=
    grpOK_sound Tg (fun j hj => (hT j hj).1) hpts hTg
  set Tp := closure (Tg '' {j | j < tg.length}) with hTpdef
  have hTX : Tp ≤ X := by
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact (hT j hj).2
  set xv : ℕ → Equiv.Perm (Fin 315) := fun k => wordP Tg (tW.getD (getN xI k) [])
  set Qv : ℕ → Equiv.Perm (Fin 315) := fun k => xv k * xv k
  have hxk : ∀ k < 4, getN xI k < 128 ∧ PRep (getN qg k) (Qv k) ∧ xv k ∈ Tp := by
    intro k hk
    have e := allN_spec hxs k hk
    rw [strictB_eq', bAnd_eq, Bool.and_eq_true, Nat.blt_eq, strictB_eq'] at e
    obtain ⟨hi, e⟩ := e
    have hi' : getN xI k < tW.length := by rw [h128]; exact hi
    have hr := hTrep _ hi'
    exact ⟨hi, prep_of_eq e (prep_pm hr hr), (hTmem _).2 ⟨_, hi', rfl⟩⟩
  have hQ : ∀ k < qg.length, PRep (getN qg k) (Qv k) := fun k hk =>
    (hxk k (by rw [hq4] at hk; exact hk)).2.1
  have hw := w_ok
  unfold ckW at hw
  rw [bAnd_eq, Bool.and_eq_true] at hw
  obtain ⟨hWg, hWn⟩ := hw
  obtain ⟨hWmem, -, -, hWrep, -, -⟩ := grpOK_sound Qv hQ hpts hWg
  set Wp := closure (Qv '' {k | k < qg.length}) with hWpdef
  have hQW : ∀ k < 4, Qv k ∈ Wp := fun k hk =>
    subset_closure ⟨k, by rw [Set.mem_setOf_eq, hq4]; exact hk, rfl⟩
  have hWT : Wp ≤ closure ((fun x : Equiv.Perm (Fin 315) => x ^ 2) '' (Tp : Set _)) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 4 := by rw [Set.mem_setOf_eq, hq4] at hk; exact hk
    exact subset_closure ⟨xv k, (hxk k hk').2.2, pow_two _⟩
  have hWX : Wp ≤ X := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 4 := by rw [Set.mem_setOf_eq, hq4] at hk; exact hk
    exact mul_mem (hTX (hxk k hk').2.2) (hTX (hxk k hk').2.2)
  have hc := c_ok
  unfold ckC at hc
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenN_eq] at hc
  obtain ⟨h14, hshape, horb⟩ := hc
  obtain ⟨-, hC⟩ := vals vals_c
  obtain ⟨-, hCi⟩ := vals vals_ci
  set κ : ℕ → Equiv.Perm (Fin 315) := fun i => wordP σ0 (gcw.getD i [])
  have hinv := invs_ok
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hinv
  obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := hinv
  obtain ⟨hcl, hce⟩ := invsOK_sound (X := κ) (Y := fun i => wordP σ0 (gciw.getD i []))
    (fun i hi => (hC i hi).1) (fun i hi => (hCi i hi).1) hi1
  have hCr : ∀ i < 14, PRep (getN gc i) (κ i) := fun i hi => (hC i (by rw [h14]; exact hi)).1
  have hCir : ∀ i < 14, PRep (getN gci i) (κ i)⁻¹ := by
    intro i hi
    have := (hCi i (by rw [hcl, h14]; exact hi)).1
    rwa [hce i (by rw [h14]; exact hi)] at this
  have hCX : ∀ i < gc.length, κ i ∈ X := fun i hi => (hC i hi).2
  have hnorm := normOK_sound (η := κ) (fun g hg => hCr g (by have hg' : g < 2 := hg; omega)) hQ hWrep hWn
  set Np := closure (κ '' {g | g < 2}) with hNpdef
  have hNW : Np ≤ normalizer (Wp : Set (Equiv.Perm (Fin 315))) := by
    apply CFSG.RankThree.Native.closure_le_normalizer_closure
    rintro _ ⟨g, hg, rfl⟩ _ ⟨k, hk, rfl⟩
    obtain ⟨q, hq, e⟩ := hnorm g hg k hk
    have e2 : κ g * Qv k * (κ g)⁻¹ = wordP Qv (wW.getD q []) := by
      rw [e]
      group
    rw [e2]
    exact (hWmem _).2 ⟨q, hq, rfl⟩
  have hNX : Np ≤ X := by
    rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hCX g (by rw [h14]; exact lt_trans hg (by norm_num))
  have hQi : ∀ k < 4, PRep (getN qgi k) (Qv k)⁻¹ := by
    have hcube := cubeOK_sound hQ hi3
    have hqil : qgi.length = qg.length := by
      unfold cubeOK at hi3
      rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, lenN_eq, lenN_eq] at hi3
      exact hi3.1
    obtain ⟨-, e⟩ := invsOK_sound (X := Qv) (Y := fun k => Qv k * (Qv k * Qv k)) hQ
      (fun k hk => hcube k (by rw [← hqil]; exact hk)) hi2
    intro k hk
    have hk' : k < qg.length := by rw [hq4]; exact hk
    have := hcube k hk'
    rwa [e k hk'] at this
  have pYi : PRep ygi Y⁻¹ := by
    have h4 := prep_of_eq hi5 (prep_pm pY (prep_pm pY (prep_pm pY pY)))
    have e := (prep_eq (prep_pm pY h4) prep_one).1 hi4
    rwa [← inv_eq_of_mul_eq_one_right e] at h4
  obtain ⟨-, hS⟩ := vals vals_s
  have hs := s_ok
  unfold ckS at hs
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, strictB_eq', bAnd_eq, bAnd_eq, bAnd_eq] at hs
  simp only [Bool.and_eq_true, Nat.beq_eq, lenW_eq, lenN_eq, Nat.blt_eq] at hs
  obtain ⟨hSg, h27, hs2, hzi, hy5, hz1, hz0, hz1', hzy⟩ := hs
  set Sg : ℕ → Equiv.Perm (Fin 315) := fun k => wordP σ0 (sw.getD k [])
  have hSr : ∀ j < sg.length, PRep (getN sg j) (Sg j) := fun j hj => (hS j hj).1
  obtain ⟨hSmem, hScard, -, hSrep, -, -⟩ := grpOK_sound Sg hSr hpts hSg
  set Sp := closure (Sg '' {j | j < sg.length}) with hSpdef
  set z0 := wordP Sg (sW.getD zi []) with hz0def
  have pz := hSrep zi hzi
  have hSX : Sp ≤ X := by
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact (hS j hj).2
  have hzC : Sp ≤ centralizer ({z0} : Set (Equiv.Perm (Fin 315))) := by
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj2 : j < 2 := by rw [Set.mem_setOf_eq, hs2] at hj; exact hj
    rw [SetLike.mem_coe]
    apply mem_cent_of
    interval_cases j
    · exact (comm_sound pz (hSr 0 (by rw [hs2]; norm_num)) hz0).symm
    · exact (comm_sound pz (hSr 1 (by rw [hs2]; norm_num)) hz1').symm
  have hY5 : Y ^ 5 = 1 ∧ Y ≠ 1 := by
    unfold ord5 at hy5
    rw [bAnd_eq, Bool.and_eq_true] at hy5
    refine ⟨?_, ne_one_sound pY hy5.2⟩
    have e := (prep_eq (prep_pm pY (prep_pm pY (prep_pm pY (prep_pm pY pY)))) prep_one).1 hy5.1
    rw [← e]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  obtain ⟨hFl, hF⟩ := vals vals_f
  have hf := f_ok
  unfold ckF at hf
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at hf
  simp only [Bool.and_eq_true, Nat.beq_eq, lenW_eq, lenN_eq] at hf
  obtain ⟨hf4, hAg, h25, hKg, h4, hc0, hc1, hc2, hc3, ht3⟩ := hf
  set Fv : ℕ → Equiv.Perm (Fin 315) := fun k => wordP σ0 (fw.getD k [])
  have hFr : ∀ k < 4, PRep (getN fg k) (Fv k) := fun k hk => (hF k (by rw [hf4]; exact hk)).1
  have hFX : ∀ k < 4, Fv k ∈ X := fun k hk => (hF k (by rw [hf4]; exact hk)).2
  have hFC : ∀ k < 4, Fv k ∈ X ⊓ centralizer {Y} := by
    intro k hk
    refine mem_inf.2 ⟨hFX k hk, mem_cent_of ?_⟩
    interval_cases k
    · exact comm_sound (hFr 0 (by norm_num)) pY hc0
    · exact comm_sound (hFr 1 (by norm_num)) pY hc1
    · exact comm_sound (hFr 2 (by norm_num)) pY hc2
    · exact comm_sound (hFr 3 (by norm_num)) pY hc3
  set σA : ℕ → Equiv.Perm (Fin 315) := fun i => [Y, Fv 0].getD i 1
  have hAr : ∀ j < [yg, getN fg 0].length, PRep (getN [yg, getN fg 0] j) (σA j) := by
    intro j hj
    have hj2 : j < 2 := hj
    interval_cases j
    · exact pY
    · exact hFr 0 (by norm_num)
  obtain ⟨-, hAcard, -, -, -, -⟩ := grpOK_sound σA hAr hpts hAg
  set σK : ℕ → Equiv.Perm (Fin 315) := fun i => [Fv 1, Fv 2].getD i 1
  have hKr : ∀ j < [getN fg 1, getN fg 2].length,
      PRep (getN [getN fg 1, getN fg 2] j) (σK j) := by
    intro j hj
    have hj2 : j < 2 := hj
    interval_cases j
    · exact hFr 1 (by norm_num)
    · exact hFr 2 (by norm_num)
  obtain ⟨-, hKcard, -, -, -, -⟩ := grpOK_sound σK hKr hpts hKg
  have hC300 : 300 ≤ Nat.card ↥(X ⊓ centralizer {Y}) := by
    refine cent_ge (A := closure (σA '' {j | j < [yg, getN fg 0].length}))
      (K := closure (σK '' {j | j < [getN fg 1, getN fg 2].length})) (T := zpowers (Fv 3))
      ?_ ?_ ?_ (by rw [hAcard, h25]) (by rw [hKcard, h4]) ?_
    · rw [closure_le]
      rintro _ ⟨j, hj, rfl⟩
      have hj2 : j < 2 := hj
      interval_cases j
      · exact mem_inf.2 ⟨mY, mem_cent_of rfl⟩
      · exact hFC 0 (by norm_num)
    · rw [closure_le]
      rintro _ ⟨j, hj, rfl⟩
      have hj2 : j < 2 := hj
      interval_cases j
      · exact hFC 1 (by norm_num)
      · exact hFC 2 (by norm_num)
    · rw [zpowers_le]
      exact hFC 3 (by norm_num)
    · unfold ord3 at ht3
      rw [bAnd_eq, Bool.and_eq_true] at ht3
      have e := (prep_eq (prep_pm (hFr 3 (by norm_num)) (prep_pm (hFr 3 (by norm_num))
        (hFr 3 (by norm_num)))) prep_one).1 ht3.1
      have hp : Fv 3 ^ 3 = 1 := by
        rw [← e]
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [Nat.card_zpowers, orderOf_eq_prime hp (ne_one_sound (hFr 3 (by norm_num)) ht3.2)]
  have hcls := card_cent_le X (x := Y) (m := Nat.card {y | ∃ k ∈ X, y = k⁻¹ * Y * k}) le_rfl
  have hcls2 : Nat.card {y | ∃ k ∈ X, y = k⁻¹ * Y * k} ≤ 2016 := by
    have h1 : 300 * Nat.card {y | ∃ k ∈ X, y = k⁻¹ * Y * k} ≤ 300 * 2016 := by
      calc 300 * Nat.card {y | ∃ k ∈ X, y = k⁻¹ * Y * k}
          ≤ Nat.card ↥(X ⊓ centralizer {Y}) * Nat.card {y | ∃ k ∈ X, y = k⁻¹ * Y * k} :=
            Nat.mul_le_mul_right _ hC300
        _ ≤ Nat.card X := hcls
        _ = 300 * 2016 := by rw [hXc]
    exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
  have hcover := orbOK_cover κ Y hcl (fun i hi => hCr i (by rw [← h14]; exact hi))
    (fun i hi => hCir i (by rw [← h14]; exact hi)) pY hpts horb X hCX hcls2
  have hgen := genOK_sound prep_a prep_b pY
    pYi hCr hCir (fun k hk => hQ k (by rw [hq4]; exact hk)) hQi hQW g_ok
  refine ⟨Tp, Wp, Sp, z0, Y, hTX, by rw [hTcard, h128], hWX, hWT, hSX, by rw [hScard, h27],
    ne_one_sound pz hz1, (hSmem _).2 ⟨zi, hzi, rfl⟩, hzC, mY, hY5.1, hY5.2,
    comm_sound pz pY hzy, ?_⟩
  intro g hg
  obtain ⟨r, hr, hlet, e⟩ := hcover g⁻¹ (inv_mem hg)
  rw [inv_inv] at e
  obtain ⟨c, hs, hrw, hc2, hc14, hhs⟩ := shapeOK_sound hshape r hr
  obtain ⟨j, rfl⟩ : ∃ j, c = 2 + j := ⟨c - 2, by omega⟩
  have hj : j < 12 := by omega
  rw [hrw] at hlet e
  rw [wordP_cons κ (fun i hi => hCr i (by rw [← h14]; exact hi)) hlet] at e
  set H := wordP κ hs with hHdef
  have hHN : H ∈ Np := wordP_mem Np (fun i hi => subset_closure ⟨i, hi, rfl⟩) hhs
  have e2 : g * Y * g⁻¹ = H⁻¹ * ((κ (2 + j))⁻¹ * Y * κ (2 + j)) * H⁻¹⁻¹ := by
    rw [e]
    group
  rw [e2]
  have hXR : X ≤ Wp ⊔ zpowers ((κ (2 + j))⁻¹ * Y * κ (2 + j)) := by
    rw [hXdef, genGroup, closure_le]
    rintro _ (rfl | rfl)
    · exact (hgen j hj).1
    · exact (hgen j hj).2
  intro x hx
  refine mem_sup_zpowers_conj (hNW (inv_mem hHN)) (hXR ?_)
  rw [inv_inv]
  exact mul_mem (mul_mem (hNX hHN) hx) (inv_mem (hNX hHN))

end CFSG.KD.KS152Gen

end
