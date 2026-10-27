module

public import Certificates.Kernel.Ivk8NormP.M11
public import CFSG.Certificates.Kernel.Ivk8NormPCGlue
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

set_option maxRecDepth 100000

namespace CFSG.KS.Ivk8NormP.M11

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.Sporadic.Schreier
  CFSG.Certificates CFSG.KS.PK Subgroup CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem gens_eq : gens.map pkp = [m11gA, m11gB] := by
  rw [eq_of_vals (l₂ := [codeV m11gA, codeV m11gB]) ch5253_m11_gens]
  simp [pkp_codeV]

theorem gens_mem : ∀ g ∈ [m11gA, m11gB], g ∈ NativeSporadic.M11 := fun g hg => by
  rw [m11_eq]
  exact subset_closure (by simpa using hg)

theorem ev_mem (w : List ℤ) : pkp (evV gens w) ∈ NativeSporadic.M11 := by
  rw [pkp_evV, gens_eq]
  exact evalCodes_mem _ gens_mem w

theorem a_eq : pkp a = m11gA := by
  change pkp (gens.getD 0 (oneV 11)) = _
  rw [eq_of_vals (l₂ := [codeV m11gA, codeV m11gB]) ch5253_m11_gens]
  simp [pkp_codeV]

theorem card_M11 : Nat.card NativeSporadic.M11 = 7920 := by
  rw [← m11Certificate_originalSubgroup, ← m11Certificate.orderCertificate_eq_card
    m11Certificate_check.1, m11Certificate_check.2]

theorem strong_eq : m11Certificate.strong.toList = (buildV gens m11Words).map pkp := by
  have e1 : m11Certificate = certificate (by decide) (gens.map pkp) m11Words #v[0, 1, 2, 3]
      (by decide) := by
    rw [gens_eq]
    rfl
  rw [e1]
  exact certificate_strong_eq _ _ _ _ _ _ rfl

theorem mem_iff (y : Equiv.Perm (Fin 11)) :
    y ∈ NativeSporadic.M11 ↔ y ∈ (enumV (buildV gens m11Words) #v[0, 1, 2, 3]).map pkp := by
  rw [← m11Certificate_originalSubgroup, ← mem_enumeration_iff m11Certificate
    m11Certificate_check.1, enumeration_eq_enumV m11Certificate _ strong_eq]
  rfl

@[expose] noncomputable def eChain : RawSchreierDatum 11 :=
  certificate (by decide) (eGens.map pkp) [] #v[1] (by decide)

theorem eChain_strong : eChain.strong.toList = (buildV eGens []).map pkp :=
  certificate_strong_eq _ _ _ _ _ _ rfl

theorem eChain_valid : ValidSchreier eChain :=
  check_of_schV _ _ _ _ _ _ eChain_strong ch5253_m11_eSch

theorem eChain_card : Nat.card eChain.originalSubgroup = 9 := by
  have hb : eChain.base = #v[1] := rfl
  rw [← eChain.orderCertificate_eq_card eChain_valid,
    orderCertificate_eq_ordV eChain _ eChain_strong, hb]
  exact beq_iff_eq.1 ch5253_m11_eOrd

theorem eChain_mem (y : Equiv.Perm (Fin 11)) :
    y ∈ eChain.originalSubgroup ↔ y ∈ eEnum.map pkp := by
  rw [← mem_enumeration_iff eChain eChain_valid, enumeration_eq_enumV eChain _ eChain_strong]
  rfl

theorem eChain_le : eChain.originalSubgroup ≤ NativeSporadic.M11 := by
  rw [eChain, certificate_originalSubgroup, closure_le]
  intro g hg
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
  simp only [eGens, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact ev_mem _
  · exact ev_mem _

theorem pair_of_conj {M : Type*} [Group M] {G : Subgroup M} {g x U : M} (hg : g ∈ G) (hx : x ∈ G)
    (hU : U ∈ G) (h1 : U * U = 1)
    (h2 : (g * x * g⁻¹ * U * (g * x * g⁻¹)⁻¹) * (g * x * g⁻¹ * U * (g * x * g⁻¹)⁻¹) = 1)
    (h3 : U * (g * x * g⁻¹ * U * (g * x * g⁻¹)⁻¹) = (g * x * g⁻¹ * U * (g * x * g⁻¹)⁻¹) * U)
    (h4 : g * x * g⁻¹ * (g * x * g⁻¹ * U * (g * x * g⁻¹)⁻¹) * (g * x * g⁻¹)⁻¹ =
      U * (g * x * g⁻¹ * U * (g * x * g⁻¹)⁻¹))
    (h5 : g * x * g⁻¹ * U * (g * x * g⁻¹)⁻¹ ≠ U) :
    ∃ u ∈ G, ∃ v ∈ G, u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧ x * u * x⁻¹ = v ∧
      x * v * x⁻¹ = u * v ∧ v ≠ u := by
  set Y := g * x * g⁻¹ with hY
  set V := Y * U * Y⁻¹ with hV
  have hx' : x = g⁻¹ * Y * g := by rw [hY]; group
  refine ⟨g⁻¹ * U * g, G.mul_mem (G.mul_mem (G.inv_mem hg) hU) hg, g⁻¹ * V * g, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have hYG : Y ∈ G := G.mul_mem (G.mul_mem hg hx) (G.inv_mem hg)
    exact G.mul_mem (G.mul_mem (G.inv_mem hg) (G.mul_mem (G.mul_mem hYG hU) (G.inv_mem hYG))) hg
  · calc g⁻¹ * U * g * (g⁻¹ * U * g) = g⁻¹ * (U * U) * g := by group
      _ = 1 := by rw [h1]; group
  · calc g⁻¹ * V * g * (g⁻¹ * V * g) = g⁻¹ * (V * V) * g := by group
      _ = 1 := by rw [h2]; group
  · calc g⁻¹ * U * g * (g⁻¹ * V * g) = g⁻¹ * (U * V) * g := by group
      _ = g⁻¹ * (V * U) * g := by rw [h3]
      _ = g⁻¹ * V * g * (g⁻¹ * U * g) := by group
  · rw [hx', hV]
    group
  · calc x * (g⁻¹ * V * g) * x⁻¹ = g⁻¹ * (Y * V * Y⁻¹) * g := by rw [hx']; group
      _ = g⁻¹ * (U * V) * g := by rw [h4]
      _ = g⁻¹ * U * g * (g⁻¹ * V * g) := by group
  · intro h
    apply h5
    have := congrArg (fun z => g * z * g⁻¹) h
    simpa [mul_assoc] using this

theorem m11_hh :
    ∀ x ∈ NativeSporadic.M11, orderOf x = 3 → ∃ u ∈ NativeSporadic.M11,
      ∃ v ∈ NativeSporadic.M11, u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧ x * u * x⁻¹ = v ∧
        x * v * x⁻¹ = u * v ∧ v ≠ u := by
  classical
  intro x hx hxo
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set G := NativeSporadic.M11 with hG
  set E' : Subgroup G := eChain.originalSubgroup.subgroupOf G with hE'
  have hE'c : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe eChain_le).toEquiv, eChain_card]
  have hE'p : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hE'c]; norm_num)
  obtain ⟨T, hT⟩ := hE'p.exists_le_sylow
  have hTc : E' = (T : Subgroup G) := by
    refine Subgroup.eq_of_le_of_card_ge hT ?_
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 T.isPGroup'
    have hdvd : Nat.card T ∣ 7920 := by
      rw [← card_M11]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hm] at hdvd
    have hm2 : m ≤ 2 := by
      by_contra h
      have h27 : 3 ^ 3 ∣ 3 ^ m := pow_dvd_pow 3 (by omega)
      have := h27.trans hdvd
      norm_num at this
    rw [hE'c, hm]
    calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 9 := by norm_num
  set x' : G := ⟨x, hx⟩ with hx'
  have hx'o : orderOf x' = 3 := by rw [hx', Subgroup.orderOf_mk]; exact hxo
  have hzp : IsPGroup 3 (zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'o, pow_one])
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hgx : g * x' * g⁻¹ ∈ (T : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x' (MulAut.conj g) _ (hS (mem_zpowers x'))
  rw [← hTc, hE', Subgroup.mem_subgroupOf] at hgx
  have hyE : (g : Equiv.Perm (Fin 11)) * x * (g : Equiv.Perm (Fin 11))⁻¹ ∈
      eChain.originalSubgroup := by
    simpa [hx'] using hgx
  obtain ⟨y', hy', hyy⟩ := List.mem_map.1 ((eChain_mem _).1 hyE)
  have hy1 : pkp y' ≠ 1 := by
    rw [hyy]
    intro h1
    have h2 : x = 1 := by
      have := congrArg (fun z => (g : Equiv.Perm (Fin 11))⁻¹ * z * g) h1
      simpa [mul_assoc] using this
    rw [h2, orderOf_one] at hxo
    norm_num at hxo
  obtain ⟨u₀, hu₀, h1, h2, h3, h4, h5⟩ := hhAll_spec ch5253_m11_hh y' hy' hy1
  rw [hyy] at h2 h3 h4 h5
  have hU : pkp u₀ ∈ G := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hu₀
    exact ev_mem w
  exact pair_of_conj g.2 hx hU h1 h2 h3 h4 h5

theorem mem_ps {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h : p ∣ 7920) :
    p ∈ [5, 11] := by
  have hpm : p ∈ Nat.primeFactorsList 7920 :=
    (Nat.mem_primeFactorsList (by norm_num)).2 ⟨hp, h⟩
  have hf : Nat.primeFactorsList 7920 = [2, 2, 2, 2, 3, 3, 5, 11] := by norm_num
  rw [hf] at hpm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm ⊢
  omega

theorem m11_noP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 11)), P ≤ NativeSporadic.M11 → W ≤ NativeSporadic.M11 →
      Nat.card P = 2 ^ 4 → IsPGroup p W → P ≤ normalizer (W : Set (Equiv.Perm (Fin 11))) →
      W = ⊥ := by
  have hwd : wd 11 = 4 := by decide
  have hw : chkPC 11 (wd 11) a.1.1 [5, 11] [witsF (oneV 11) xs, witsF c1 xs, witsF c2 xs]
      ((enumV (buildV gens m11Words) #v[0, 1, 2, 3]).map fun y => y.1.1) = true := by
    rw [hwd]
    exact ch5253_m11_w
  refine noP_of_chkPC (by norm_num) (by rw [hwd]; norm_num) le_rfl hp hp2 ch5253_m11_xs ?_
    List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) ch5253_m11_klein (ev_mem wCB)
    (ev_mem wCAB) ch5253_m11_conj (fun y hy => List.mem_map.1 ((mem_iff y).1 hy)) ?_ hw ?_
  · intro x hx
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [a_eq]
      exact gens_mem _ (by simp)
    · exact ev_mem _
  · intro y hy hyo
    refine mem_ps hp hp2 hp3 ?_
    rw [← card_M11, ← hyo, ← Subgroup.orderOf_mk y hy]
    exact orderOf_dvd_natCard _
  · rw [card_M11]
    norm_num

end CFSG.KS.Ivk8NormP.M11

end
