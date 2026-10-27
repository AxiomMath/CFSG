module

public import Certificates.Kernel.TwoAC.Prog
public import CFSG.Certificates.Kernel.TwoAC.Spin
public import Certificates.Kernel.TwoAC.Check3
public import Certificates.Kernel.TwoAC.Check4
public import Certificates.Kernel.TwoAC.Check5

public section

namespace CertificateChecks.KernelTwoAC

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.KC.BM.SL CFSG.KC.BM.TwoAC CertificateChecks.KernelBM.FiveA
  Module
open scoped Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "Vec" => Fin 4370 → ZMod 2
local notation "mA" => stripMat CFSG.KC.BM.Seeds.A1
local notation "mB" => stripMat CFSG.KC.BM.Seeds.A2
local notation "aM" => aW mA mB
local notation "bM" => bW mA mB
local notation "xM" => xW mA mB

set_option maxRecDepth 100000

@[expose] noncomputable def code (t : ℕ) : ℕ := codeAt TwoAC.Fb t

@[expose] noncomputable def Dm (l : ℕ) : MatB := if l = 0 then aM else bM

@[expose] noncomputable def rho (k i : ℕ) : Vec :=
  if i = 0 then vrow (rowOf TwoAC.V0 k) else vrow (rowOf TwoAC.V1 k)

theorem vrow_rowOf_zero (t : ℕ) : vrow (rowOf 0 t) = 0 := by
  funext j
  rw [vrow_rowOf]
  simp

theorem forest_valid : ForestOK 4370 code := by
  intro t ht hc
  unfold code at hc
  exact ((forestOK_sound TwoAC.forest0 t ht).2 (by omega)).1

theorem spin_of_forest {S SA SB : List Nat} {k : ℕ} (hSA : stripMat S * aM = stripMat SA)
    (hSB : stripMat S * bM = stripMat SB)
    (h : forestOK TwoAC.Fb S SA SB TwoAC.V0 TwoAC.V1 k = true) :
    SpinRel code Dm (rho k) (stripMat S) := by
  intro t
  obtain ⟨hr, hc⟩ := forestOK_sound h t.val t.isLt
  rw [stripMat_row]
  unfold code
  split_ifs with h1 h2
  · obtain ⟨hlt, he⟩ := hr (by omega)
    rw [he, rho]
    by_cases h0 : codeAt TwoAC.Fb t.val = 8740
    · rw [if_pos h0, if_pos (by omega)]
    · rw [if_neg h0, if_neg (by omega)]
  · obtain ⟨hlt, he⟩ := hc (by omega)
    rw [he, ← rowMul]
    by_cases h0 : codeAt TwoAC.Fb t.val % 2 = 0
    · rw [if_pos h0, h0, Dm, if_pos rfl, hSA, stripMat_row]
    · rw [if_neg h0, Dm, if_neg h0, hSB, stripMat_row]
  · exfalso
    obtain ⟨hlt, -⟩ := hc (by omega)
    omega

theorem prodA {S SA : List Nat} (hS : wfMat S = true) (h : AllStrips [TwoAC.a] S SA) :
    stripMat S * aM = stripMat SA := by
  rw [← e_a]
  exact mul1 hS TwoAC.wf_a h

theorem prodB {S SB : List Nat} (hS : wfMat S = true) (h : AllStrips [TwoAC.w2] S SB) :
    stripMat S * bM = stripMat SB := by
  rw [← e_b]
  exact mul1 hS TwoAC.wf_w2 h

theorem rho_one : rho 1 = fun i => rho 0 i ᵥ* xM := by
  funext i
  have e0 : rowOf (mulS TwoAC.x TwoAC.V0) 0 = rowOf TwoAC.V0 1 := Nat.eq_of_beq_eq_true TwoAC.xV0
  have e1 : rowOf (mulS TwoAC.x TwoAC.V1) 0 = rowOf TwoAC.V1 1 := Nat.eq_of_beq_eq_true TwoAC.xV1
  unfold rho
  split_ifs
  · rw [← e0, mulS_rows TwoAC.wf_x _ (by norm_num), e_x]
  · rw [← e1, mulS_rows TwoAC.wf_x _ (by norm_num), e_x]

theorem mem0 (k : ℕ) (hk : k < 64) : vrow (rowOf TwoAC.V0 k) ᵥ* stripMat TwoAC.th0 = 0 := by
  have e : mulS TwoAC.th0 TwoAC.V0 = 0 := Nat.eq_of_beq_eq_true TwoAC.ker0
  rw [← mulS_rows TwoAC.wf_th0 _ hk, e, vrow_rowOf_zero]

theorem mem1 (k : ℕ) (hk : k < 64) : vrow (rowOf TwoAC.V1 k) ᵥ* stripMat TwoAC.th1 = 0 := by
  have e : mulS TwoAC.th1 TwoAC.V1 = 0 := Nat.eq_of_beq_eq_true TwoAC.ker1
  rw [← mulS_rows TwoAC.wf_th1 _ hk, e, vrow_rowOf_zero]

theorem ker0_dim : finrank (ZMod 2) (kerL (stripMat TwoAC.th0)) ≤ 3 := by
  have h : 4367 ≤ (stripMat TwoAC.th0).rank := le_rank_of_shape (k := 4367) (by norm_num)
    TwoAC.wf_th0 TwoAC.wf_Pt0 TwoAC.wf_Qt0 (by bm_strips4 CFSG.KC.BM.TwoAC.cPt0 69)
    TwoAC.shape_t0
  have := finrank_kerL (stripMat TwoAC.th0)
  omega

theorem ker1_dim : finrank (ZMod 2) (kerL (stripMat TwoAC.th1)) ≤ 4 := by
  have h : 4366 ≤ (stripMat TwoAC.th1).rank := le_rank_of_shape (k := 4366) (by norm_num)
    TwoAC.wf_th1 TwoAC.wf_Pt1 TwoAC.wf_Qt1 (by bm_strips4 CFSG.KC.BM.TwoAC.cPt1 69)
    TwoAC.shape_t1
  have := finrank_kerL (stripMat TwoAC.th1)
  omega

theorem exists_comb_of_dims {K : Type*} [Field K] {m n : ℕ} (K0 K1 : Submodule K (Fin m → K))
    (b : Fin n → (Fin m → K) × (Fin m → K))
    (hb : ∀ k, (b k).1 ∈ K0 ∧ (b k).2 ∈ K1) (hli : LinearIndependent K b)
    (hd : finrank K K0 + finrank K K1 ≤ n) (v : (Fin m → K) × (Fin m → K))
    (hv : v.1 ∈ K0 ∧ v.2 ∈ K1) : ∃ c : Fin n → K, ∑ k, c k • b k = v := by
  let β : Fin n → K0 × K1 := fun k => (⟨(b k).1, (hb k).1⟩, ⟨(b k).2, (hb k).2⟩)
  have hβ : LinearIndependent K β :=
    LinearIndependent.of_comp (K0.subtype.prodMap K1.subtype) hli
  have hfin : finrank K (K0 × K1) = n := by
    have h := hβ.fintype_card_le_finrank
    rw [Module.finrank_prod, Fintype.card_fin] at h
    rw [Module.finrank_prod]
    omega
  have hspan := hβ.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hfin])
  have hmem : ((⟨v.1, hv.1⟩, ⟨v.2, hv.2⟩) : K0 × K1) ∈ Submodule.span K (Set.range β) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨c, Prod.ext ?_ ?_⟩
  · have e := congrArg (fun q : K0 × K1 => (q.1 : Fin m → K)) hc
    simpa [β, Prod.fst_sum, Submodule.coe_sum] using e
  · have e := congrArg (fun q : K0 × K1 => (q.2 : Fin m → K)) hc
    simpa [β, Prod.snd_sum, Submodule.coe_sum] using e

set_option synthInstance.maxHeartbeats 400000 in
theorem roots_comb {M : MatB} (hMa : M * aM = aM * M) (hMb : M * bM = bM * M) :
    ∃ cc : Fin 7 → ZMod 2, (fun i => rho 0 i ᵥ* M) = ∑ k : Fin 7, cc k • rho k.val := by
  have hca : Commute M aM := hMa
  have hcb : Commute M bM := hMb
  have h0 : Commute M (stripMat TwoAC.th0) := by
    rw [th0_eq]
    exact ((hcb.mul_right hca).add_right ((hca.mul_right hcb).mul_right hcb)).add_right hca
  have h1 : Commute M (stripMat TwoAC.th1) := by
    rw [th1_eq]
    exact ((hcb.add_right ((hca.mul_right hcb).mul_right hcb)).add_right
      ((hcb.mul_right hcb).mul_right hcb)).add_right (Commute.one_right M)
  have hli : LinearIndependent (ZMod 2)
      (fun j : Fin 7 => (vrow (rowOf TwoAC.V0 j.val), vrow (rowOf TwoAC.V1 j.val))) :=
    rowsNZ_sound TwoAC.indep
  have hp0 : rho 0 0 ᵥ* M ∈ kerL (stripMat TwoAC.th0) := by
    rw [mem_kerL, Matrix.vecMul_vecMul, h0.eq, ← Matrix.vecMul_vecMul, rho, if_pos rfl,
      mem0 0 (by norm_num), Matrix.zero_vecMul]
  have hp1 : rho 0 1 ᵥ* M ∈ kerL (stripMat TwoAC.th1) := by
    rw [mem_kerL, Matrix.vecMul_vecMul, h1.eq, ← Matrix.vecMul_vecMul, rho,
      if_neg one_ne_zero, mem1 0 (by norm_num), Matrix.zero_vecMul]
  have hd : finrank (ZMod 2) (kerL (stripMat TwoAC.th0)) +
      finrank (ZMod 2) (kerL (stripMat TwoAC.th1)) ≤ 7 := by
    have := ker0_dim
    have := ker1_dim
    omega
  obtain ⟨cc, hcc⟩ := exists_comb_of_dims (K := ZMod 2) (kerL (stripMat TwoAC.th0))
    (kerL (stripMat TwoAC.th1))
    (fun j : Fin 7 => (vrow (rowOf TwoAC.V0 j.val), vrow (rowOf TwoAC.V1 j.val)))
    (fun k => ⟨mem_kerL.2 (mem0 k.val (by omega)), mem_kerL.2 (mem1 k.val (by omega))⟩) hli
    hd (rho 0 0 ᵥ* M, rho 0 1 ᵥ* M) ⟨hp0, hp1⟩
  have e0 := congrArg Prod.fst hcc
  have e1 := congrArg Prod.snd hcc
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd] at e0 e1
  refine ⟨cc, ?_⟩
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  by_cases hi : i = 0
  · subst hi
    simp only [rho, if_pos rfl] at e0 ⊢
    exact e0.symm
  · simp only [rho, if_neg hi, if_neg one_ne_zero] at e1 ⊢
    exact e1.symm

@[expose] noncomputable def tauL (u v : Vec) (D : MatB) : MatB →ₗ[ZMod 2] Vec where
  toFun N := u ᵥ* N + (v ᵥ* N) ᵥ* D
  map_add' N N' := by
    simp only [Matrix.vecMul_add, Matrix.add_vecMul]
    abel
  map_smul' r N := by
    simp only [Matrix.vecMul_smul, Matrix.smul_vecMul, RingHom.id_apply, smul_add]

theorem tauL_apply (u v : Vec) (D N : MatB) : tauL u v D N = u ᵥ* N + (v ᵥ* N) ᵥ* D := rfl

theorem tauL_comm {u v : Vec} {D Bm N : MatB} (hu : u ᵥ* Bm = (v ᵥ* Bm) ᵥ* D)
    (hN : N * D = D * N) : tauL u v D (Bm * N) = 0 := by
  rw [tauL_apply, ← Matrix.vecMul_vecMul, hu, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    ← Matrix.vecMul_vecMul v Bm N, Matrix.vecMul_vecMul _ N D, hN, ← Matrix.vecMul_vecMul]
  exact CharTwo.add_self_eq_zero _

theorem beta_rows {Bt : Nat} {D : List Nat} (hD : wfMat D = true)
    (h : Nat.beq (mulS TwoAC.Bv Bt) (mulS D (mulS TwoAC.Bv CFSG.KC.BM.Seeds.A1.s0)) = true)
    {t : ℕ} (ht : t < 64) :
    vrow (rowOf Bt t) ᵥ* stripMat TwoAC.Bv =
      (vrow (rowOf CFSG.KC.BM.Seeds.A1.s0 t) ᵥ* stripMat TwoAC.Bv) ᵥ* stripMat D := by
  rw [← mulS_rows TwoAC.wf_Bv _ ht, Nat.eq_of_beq_eq_true h, mulS_rows hD _ ht,
    mulS_rows TwoAC.wf_Bv _ ht]

theorem commutant : ∃ T₁ T₂ : MatB, T₁.rank ≤ 1 ∧ T₂.rank ≤ 78 ∧
    ∀ M : MatB, M * aM = aM * M → M * bM = bM * M →
      ∃ c : Fin 4 → ZMod 2, M = c 0 • 1 + c 1 • xM + c 2 • T₁ + c 3 • T₂ := by
  have hBi : stripMat TwoAC.Binv * stripMat TwoAC.Bv = 1 :=
    one1 TwoAC.wf_Binv TwoAC.wf_Bv (by bm_strips4 CFSG.KC.BM.TwoAC.cBinv 69)
  have sp0 : SpinRel code Dm (rho 0) (stripMat TwoAC.Bv) :=
    spin_of_forest (prodA TwoAC.wf_Bv (by bm_strips4 CFSG.KC.BM.TwoAC.cBvA 69))
      (prodB TwoAC.wf_Bv (by bm_strips4 CFSG.KC.BM.TwoAC.cBvB 69)) TwoAC.forest0
  have sp2 : SpinRel code Dm (rho 2) (stripMat TwoAC.S2) :=
    spin_of_forest (prodA TwoAC.wf_S2 (by bm_strips4 CFSG.KC.BM.TwoAC.cS2A 69))
      (prodB TwoAC.wf_S2 (by bm_strips4 CFSG.KC.BM.TwoAC.cS2B 69)) TwoAC.forest2
  have sp3 : SpinRel code Dm (rho 3) (stripMat TwoAC.S3) :=
    spin_of_forest (prodA TwoAC.wf_S3 (by bm_strips4 CFSG.KC.BM.TwoAC.cS3A 69))
      (prodB TwoAC.wf_S3 (by bm_strips4 CFSG.KC.BM.TwoAC.cS3B 69)) TwoAC.forest3
  have sp4 : SpinRel code Dm (rho 4) (stripMat TwoAC.S4) :=
    spin_of_forest (prodA TwoAC.wf_S4 (by bm_strips4 CFSG.KC.BM.TwoAC.cS4A 69))
      (prodB TwoAC.wf_S4 (by bm_strips4 CFSG.KC.BM.TwoAC.cS4B 69)) TwoAC.forest4
  have sp5 : SpinRel code Dm (rho 5) (stripMat TwoAC.S5) :=
    spin_of_forest (prodA TwoAC.wf_S5 (by bm_strips4 CFSG.KC.BM.TwoAC.cS5A 69))
      (prodB TwoAC.wf_S5 (by bm_strips4 CFSG.KC.BM.TwoAC.cS5B 69)) TwoAC.forest5
  have sp6 : SpinRel code Dm (rho 6) (stripMat TwoAC.S6) :=
    spin_of_forest (prodA TwoAC.wf_S6 (by bm_strips4 CFSG.KC.BM.TwoAC.cS6A 69))
      (prodB TwoAC.wf_S6 (by bm_strips4 CFSG.KC.BM.TwoAC.cS6B 69)) TwoAC.forest6
  have hxD : ∀ l, xM * Dm l = Dm l * xM := by
    intro l
    unfold Dm
    split_ifs
    · exact a_comm.symm
    · exact b_comm.symm
  have sp1 : SpinRel code Dm (rho 1) (stripMat TwoAC.Bv * xM) := by
    rw [rho_one]
    exact spinRel_mul sp0 hxD
  let Sp : Fin 7 → MatB := ![stripMat TwoAC.Bv, stripMat TwoAC.Bv * xM, stripMat TwoAC.S2,
    stripMat TwoAC.S3, stripMat TwoAC.S4, stripMat TwoAC.S5, stripMat TwoAC.S6]
  have spk : ∀ k : Fin 7, SpinRel code Dm (rho k.val) (Sp k) := by
    intro k
    fin_cases k
    · exact sp0
    · exact sp1
    · exact sp2
    · exact sp3
    · exact sp4
    · exact sp5
    · exact sp6
  have ha := e_a
  have hb := e_b
  have tz : ∀ t < 64, ∀ (Bt : Nat) (D : List Nat), wfMat D = true →
      Nat.beq (mulS TwoAC.Bv Bt) (mulS D (mulS TwoAC.Bv CFSG.KC.BM.Seeds.A1.s0)) = true →
      (stripMat D = aM ∨ stripMat D = bM) →
      ∀ M : MatB, M * aM = aM * M → M * bM = bM * M →
        tauL (vrow (rowOf Bt t)) (vrow (rowOf CFSG.KC.BM.Seeds.A1.s0 t)) (stripMat D)
          (stripMat TwoAC.Bv * M) = 0 := by
    intro t ht Bt D hD hB hDab M hMa hMb
    apply tauL_comm (beta_rows hD hB ht)
    rcases hDab with e | e <;> rw [e]
    · exact hMa
    · exact hMb
  refine ⟨stripMat TwoAC.Binv * stripMat TwoAC.S2, stripMat TwoAC.Binv * stripMat TwoAC.S3, ?_,
    ?_, ?_⟩
  · refine (Matrix.rank_mul_le_right _ _).trans (le_of_eq ?_)
    exact rank_of_cert (by norm_num) TwoAC.wf_S2 TwoAC.wf_P2 TwoAC.wf_Q2
      (by bm_strips4 CFSG.KC.BM.TwoAC.cP2 69) TwoAC.shape2 TwoAC.ech2
  · refine (Matrix.rank_mul_le_right _ _).trans (le_of_eq ?_)
    exact rank_of_cert (by norm_num) TwoAC.wf_S3 TwoAC.wf_P3 TwoAC.wf_Q3
      (by bm_strips4 CFSG.KC.BM.TwoAC.cP3 69) TwoAC.shape3 TwoAC.ech3
  intro M hMa hMb
  obtain ⟨cc, hcc⟩ := roots_comb hMa hMb
  have spM : SpinRel code Dm (fun i => rho 0 i ᵥ* M) (stripMat TwoAC.Bv * M) := by
    refine spinRel_mul sp0 fun l => ?_
    unfold Dm
    split_ifs
    · exact hMa
    · exact hMb
  have spS := spinRel_sum Finset.univ (fun k : Fin 7 => cc k • rho k.val) (fun k => cc k • Sp k)
    (fun k _ => spinRel_smul (cc k) (spk k))
  rw [← hcc] at spS
  have hBM := spinRel_unique forest_valid spM spS
  have s0 : Sp 0 = stripMat TwoAC.Bv := rfl
  have s1 : Sp 1 = stripMat TwoAC.Bv * xM := rfl
  have s2 : Sp 2 = stripMat TwoAC.S2 := rfl
  have s3 : Sp 3 = stripMat TwoAC.S3 := rfl
  have s4 : Sp 4 = stripMat TwoAC.S4 := rfl
  have s5 : Sp 5 = stripMat TwoAC.S5 := rfl
  have s6 : Sp 6 = stripMat TwoAC.S6 := rfl
  have key : ∀ t < 64, ∀ (Bt : Nat) (D : List Nat), wfMat D = true →
      Nat.beq (mulS TwoAC.Bv Bt) (mulS D (mulS TwoAC.Bv CFSG.KC.BM.Seeds.A1.s0)) = true →
      (stripMat D = aM ∨ stripMat D = bM) →
      tauL (vrow (rowOf Bt t)) (vrow (rowOf CFSG.KC.BM.Seeds.A1.s0 t)) (stripMat D)
        (stripMat TwoAC.S2) = 0 →
      tauL (vrow (rowOf Bt t)) (vrow (rowOf CFSG.KC.BM.Seeds.A1.s0 t)) (stripMat D)
        (stripMat TwoAC.S3) = 0 →
      ∑ i : Fin 3, ![cc 4, cc 5, cc 6] i •
        tauL (vrow (rowOf Bt t)) (vrow (rowOf CFSG.KC.BM.Seeds.A1.s0 t)) (stripMat D)
          (stripMat (![TwoAC.S4, TwoAC.S5, TwoAC.S6] i)) = 0 := by
    intro t ht Bt D hD hB hDab h2 h3
    have z := tz t ht Bt D hD hB hDab M hMa hMb
    rw [hBM, map_sum] at z
    simp only [map_smul, Fin.sum_univ_seven] at z
    have z0 := tz t ht Bt D hD hB hDab 1 (by rw [one_mul, mul_one]) (by rw [one_mul, mul_one])
    have z1 := tz t ht Bt D hD hB hDab xM a_comm.symm b_comm.symm
    rw [mul_one] at z0
    rw [s0, s1, s2, s3, s4, s5, s6, z0, z1, h2, h3] at z
    simp only [smul_zero, zero_add] at z
    rw [Fin.sum_univ_three]
    exact z
  have hc3 := tests3_sound TwoAC.wf_S4 TwoAC.wf_S5 TwoAC.wf_S6 TwoAC.wf_a TwoAC.wf_w2
    TwoAC.tests ![cc 4, cc 5, cc 6] fun t ht => by
      have e2a := testN_zero TwoAC.wf_S2 TwoAC.wf_a TwoAC.wf_w2 TwoAC.test2 t ht
      have e3a := testN_zero TwoAC.wf_S3 TwoAC.wf_a TwoAC.wf_w2 TwoAC.test3 t ht
      constructor
      · exact key t ht TwoAC.betaA TwoAC.a TwoAC.wf_a TwoAC.beta_a (Or.inl ha) e2a.1 e3a.1
      · exact key t ht TwoAC.betaB TwoAC.w2 TwoAC.wf_w2 TwoAC.beta_b (Or.inr hb) e2a.2 e3a.2
  have c4 : cc 4 = 0 := by simpa using congrFun hc3 0
  have c5 : cc 5 = 0 := by simpa using congrFun hc3 1
  have c6 : cc 6 = 0 := by simpa using congrFun hc3 2
  refine ⟨![cc 0, cc 1, cc 2, cc 3], ?_⟩
  rw [Fin.sum_univ_seven, c4, c5, c6, s0, s1, s2, s3] at hBM
  simp only [zero_smul, add_zero] at hBM
  calc M = stripMat TwoAC.Binv * (stripMat TwoAC.Bv * M) := by rw [← mul_assoc, hBi, one_mul]
    _ = _ := by
      rw [hBM]
      simp only [Matrix.mul_add, Matrix.mul_smul, ← mul_assoc, hBi, one_mul, mul_one]
      rfl

theorem twoAC_fact : TwoACFact mA mB :=
  ⟨x_sq, x_rank, a_sq, b_pow, ab_pow, a_comm, b_comm, commutant⟩

end CertificateChecks.KernelTwoAC

end
