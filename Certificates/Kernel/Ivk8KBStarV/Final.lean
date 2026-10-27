module

public import CFSG.Certificates.Kernel.Ivk8KBStarVSound
public import Certificates.Kernel.Ivk8KBStarV.L34
public import Certificates.Kernel.Ivk8KBNorm.Final

public section

namespace CFSG.KS.Ivk8KBStarV.Final

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8KBStarV CFSG.Sporadic.Schreier
  CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.KS.PK CFSG.ComponentClassification.PSL3Four
  CFSG.KS.Ivk8KBNorm.Final

set_option maxRecDepth 100000

@[expose] def chainOf (ws : List (List ℤ)) {k : ℕ} (base : Vector (Fin 42) k)
    (hb : base.toList.Nodup) : RawSchreierDatum 42 :=
  certificate (by decide) (ws.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆])) [] base hb

section Chain

variable {ws : List (List ℤ)} {k : ℕ} {base : Vector (Fin 42) k} {hb : base.toList.Nodup}
  {Sc : List (VP 42)}

theorem chainOf_strong
    (hv : (Sc.map Subtype.val == ws.map fun w => (evV Ivk8Norm.L34.gens w).1) = true) :
    (chainOf ws base hb).strong.toList = Sc.map pkp := by
  have e : chainOf ws base hb = certificate (by decide)
      ((ws.map (evV Ivk8Norm.L34.gens)).map pkp) [] base hb := by
    rw [← map_evalCodes, Ivk8Norm.Final.l34_gens]
    rfl
  rw [e]
  exact certificate_strong_eq _ _ _ _ _ _ (by rw [buildV]; exact (eq_evV_of_vals hv).symm)

theorem chainOf_valid
    (hv : (Sc.map Subtype.val == ws.map fun w => (evV Ivk8Norm.L34.gens w).1) = true)
    (hs : schV Sc base = true) : ValidSchreier (chainOf ws base hb) :=
  check_of_schV _ _ _ _ _ Sc (chainOf_strong hv) hs

theorem chainOf_card
    (hv : (Sc.map Subtype.val == ws.map fun w => (evV Ivk8Norm.L34.gens w).1) = true)
    (hs : schV Sc base = true) :
    Nat.card (chainOf ws base hb).originalSubgroup = ordV Sc base := by
  rw [← (chainOf ws base hb).orderCertificate_eq_card (chainOf_valid hv hs),
    orderCertificate_eq_ordV _ Sc (chainOf_strong hv)]
  rfl

theorem chainOf_mem
    (hv : (Sc.map Subtype.val == ws.map fun w => (evV Ivk8Norm.L34.gens w).1) = true)
    (hs : schV Sc base = true) {σ : Equiv.Perm (Fin 42)}
    (h : σ ∈ (chainOf ws base hb).originalSubgroup) : σ ∈ (enumV Sc base).map pkp := by
  have e := enumeration_eq_enumV (chainOf ws base hb) Sc (chainOf_strong hv)
  change σ ∈ (enumV Sc (chainOf ws base hb).base).map pkp
  rw [← e]
  exact (mem_enumeration_iff _ (chainOf_valid hv hs) σ).2 h

theorem chainOf_le {K : Subgroup (Equiv.Perm (Fin 42))}
    (h : ∀ w ∈ ws, evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w ∈ K) :
    (chainOf ws base hb).originalSubgroup ≤ K := by
  rw [chainOf, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ ws.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆]) := hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg'
  exact h w hw

end Chain

theorem ev_comm {ws : List (List ℤ)} {Sc : List (VP 42)}
    (hv : (Sc.map Subtype.val == ws.map fun w => (evV Ivk8Norm.L34.gens w).1) = true)
    {r : Equiv.Perm (Fin 42)} (hc : ∀ s ∈ Sc, pkp s * r = r * pkp s) :
    ∀ w ∈ ws, evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w * r = r * evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w := by
  intro w hw
  have hm : evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w ∈ Sc.map pkp := by
    rw [map_pkp_of_vals hv]
    exact List.mem_map.2 ⟨w, hw, rfl⟩
  obtain ⟨s, hs, hse⟩ := List.mem_map.1 hm
  rw [← hse]
  exact hc s hs

theorem card_K₁ :
    Nat.card ↥(Subgroup.centralizer ({r₁} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 768 := by
  have h := CFSG.ComponentClassification.GrSLit.card_centralizer_mul_of_isConj
    (IsConj.refl r₁R) conjClass₁.2
  change Nat.card ↥(Subgroup.centralizer ({r₁} : Set (Equiv.Perm (Fin 42))) ⊓ R) * 315 =
    241920 at h
  omega

theorem card_K₂ :
    Nat.card ↥(Subgroup.centralizer ({r₂} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 672 := by
  have h := CFSG.ComponentClassification.GrSLit.card_centralizer_mul_of_isConj
    (IsConj.refl r₂R) conjClass₂.2
  change Nat.card ↥(Subgroup.centralizer ({r₂} : Set (Equiv.Perm (Fin 42))) ⊓ R) * 360 =
    241920 at h
  omega

theorem card_K₃ :
    Nat.card ↥(Subgroup.centralizer ({r₃} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 240 := by
  have h := CFSG.ComponentClassification.GrSLit.card_centralizer_mul_of_isConj
    (IsConj.refl r₃R) conjClass₃.2
  change Nat.card ↥(Subgroup.centralizer ({r₃} : Set (Equiv.Perm (Fin 42))) ⊓ R) * 1008 =
    241920 at h
  omega

theorem card_K₄ :
    Nat.card ↥(Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 864 := by
  have h := CFSG.ComponentClassification.GrSLit.card_centralizer_mul_of_isConj
    (IsConj.refl r₄R) conjClass₄.2
  change Nat.card ↥(Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) * 280 =
    241920 at h
  omega

theorem factorization_eq_one {p m n : ℕ} (hp : p.Prime) (hn : n = p * m) (hm : ¬ p ∣ m)
    (hm0 : m ≠ 0) : n.factorization p = 1 := by
  rw [hn, Nat.factorization_mul hp.ne_zero hm0, Finsupp.add_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm]

theorem no_elt {r : Equiv.Perm (Fin 42)} {p : ℕ}
    (hnd : ¬ p ∣ Nat.card ↥(Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ R))
    {x : Equiv.Perm (Fin 42)} (hxR : x ∈ R) (hxo : orderOf x = p) (hxc : r * x = x * r) : False := by
  have hxK : x ∈ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ R :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hxc.symm, hxR⟩
  have hd := Subgroup.orderOf_dvd_natCard _ hxK
  rw [hxo] at hd
  exact hnd hd

theorem row_packed {r : Equiv.Perm (Fin 42)} {p : ℕ} [Fact p.Prime]
    {ws : List (List ℤ)} {k : ℕ} {base : Vector (Fin 42) k} {hb : base.toList.Nodup}
    {Sc W : List (VP 42)} {wW : List (List ℤ)}
    (hv : (Sc.map Subtype.val == ws.map fun w => (evV Ivk8Norm.L34.gens w).1) = true)
    (hs : schV Sc base = true) (hSc : ∀ s ∈ Sc, pkp s * r = r * pkp s)
    (hP : ordV Sc base =
      p ^ (Nat.card ↥(Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ R)).factorization p)
    (hWv : (W.map Subtype.val == wW.map fun w => (evV Ivk8Norm.L34.gens w).1) = true)
    (hWl : ∀ w ∈ wW, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 3) (hWc : ∀ c ∈ W, pkp c * r = r * pkp c)
    (hrow : rowOK p W (enumV Sc base) = true) :
    ∀ x ∈ R, orderOf x = p → r * x = x * r →
      ∃ c ∈ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S,
        (x * (c * x * c⁻¹)) ^ p ≠ 1 := by
  intro x hxR hxo hxc
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxo
    exact (Fact.out : p.Prime).one_lt.ne hxo
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hxK : x ∈ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ R :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hxc.symm, hxR⟩
  have hPK : (chainOf ws base hb).originalSubgroup ≤
      Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ R :=
    chainOf_le fun w hw => Subgroup.mem_inf.2
      ⟨Subgroup.mem_centralizer_singleton_iff.2 (ev_comm hv hSc w hw), ev_mem_R w⟩
  obtain ⟨g, hg, hz⟩ := exists_conj_mem_of_card hPK (by rw [chainOf_card hv hs, hP]) hxK hxp hx1
  obtain ⟨hgc, hgR⟩ := Subgroup.mem_inf.1 hg
  have hgc' : Commute g r := Subgroup.mem_centralizer_singleton_iff.1 hgc
  have hz1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (conj_eq_one_iff.1 h)
  have hzp : (g * x * g⁻¹) ^ p = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
  obtain ⟨c, hcW, hne⟩ := rowOK_spec hrow _ (chainOf_mem hv hs hz) hzp hz1
  have hcS : pkp c ∈ S := by
    have hm : pkp c ∈ wW.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆]) := by
      rw [← map_pkp_of_vals hWv]
      exact List.mem_map.2 ⟨c, hcW, rfl⟩
    obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hm
    rw [← hwe]
    exact ev_mem_S w (hWl w hw)
  have hcr : Commute (pkp c) r := hWc c hcW
  refine ⟨g⁻¹ * pkp c * g⁻¹⁻¹, Subgroup.mem_inf.2
    ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, conj_mem_S (R.inv_mem hgR) hcS⟩, ?_⟩
  · exact (hgc'.inv_left.mul_left hcr).mul_left hgc'.inv_left.inv_left
  have e : x * ((g⁻¹ * pkp c * g⁻¹⁻¹) * x * (g⁻¹ * pkp c * g⁻¹⁻¹)⁻¹) =
      g⁻¹ * ((g * x * g⁻¹) * (pkp c * (g * x * g⁻¹) * (pkp c)⁻¹)) * g⁻¹⁻¹ := by
    group
  rw [e, conj_pow]
  exact fun h => hne (conj_eq_one_iff.1 h)

theorem pkp_r2 : pkp L34.r2 = r₂ := by
  rw [pkp_eq_of_val L34.ch5251_r2]
  simp [evalCodes, r₂]

theorem pkp_r3 : pkp L34.r3 = r₃ := by
  rw [pkp_eq_of_val L34.ch5251_r3]
  simp [evalCodes, r₃]

theorem comm_of {rl : VP 42} {r : Equiv.Perm (Fin 42)} (hr : pkp rl = r) {y : VP 42}
    {W : List (VP 42)} (h : commOK rl (y :: W) = true) :
    (∀ s ∈ [y], pkp s * r = r * pkp s) ∧ ∀ c ∈ W, pkp c * r = r * pkp c := by
  rw [← hr]
  exact ⟨fun s hs => commOK_spec h s (List.mem_cons.2 (Or.inl (List.mem_singleton.1 hs))),
    fun c hc => commOK_spec h c (List.mem_cons_of_mem _ hc)⟩

theorem fact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem star₁ :
    ∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₁ * x = x * r₁ →
      ∃ c ∈ C₁, (x * (c * x * c⁻¹)) ^ p ≠ 1 := by
  have hc := comm_of Ivk8Norm.Final.l34_r L34.ch5251_c03
  rintro p (rfl | rfl | rfl) x hxR hxo hxc
  · have := fact3
    exact row_packed (ws := [L34.wy03]) (hb := by decide) (wW := L34.w03)
      L34.ch5251_y03 L34.ch5251_s03 hc.1
      (by rw [beq_iff_eq.1 L34.ch5251_o03, card_K₁,
        factorization_eq_one (n := 768) (m := 256) Nat.prime_three (by norm_num) (by norm_num)
        (by norm_num)]; rfl)
      L34.ch5251_W03 (by decide) hc.2 L34.ch5251_row03 x hxR hxo hxc
  · exact (no_elt (by rw [card_K₁]; norm_num) hxR hxo hxc).elim
  · exact (no_elt (by rw [card_K₁]; norm_num) hxR hxo hxc).elim

theorem star₂ :
    ∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₂ * x = x * r₂ →
      ∃ c ∈ C₂, (x * (c * x * c⁻¹)) ^ p ≠ 1 := by
  have hc3 := comm_of pkp_r2 L34.ch5251_c13
  have hc7 := comm_of pkp_r2 L34.ch5251_c17
  rintro p (rfl | rfl | rfl) x hxR hxo hxc
  · have := fact3
    exact row_packed (ws := [[1]]) (hb := by decide) (wW := L34.w13)
      L34.ch5251_y3 L34.ch5251_s3 hc3.1
      (by rw [beq_iff_eq.1 L34.ch5251_o3, card_K₂,
        factorization_eq_one (n := 672) (m := 224) Nat.prime_three (by norm_num) (by norm_num)
        (by norm_num)]; rfl)
      L34.ch5251_W13 (by decide) hc3.2 L34.ch5251_row13 x hxR hxo hxc
  · exact (no_elt (by rw [card_K₂]; norm_num) hxR hxo hxc).elim
  · have := fact7
    exact row_packed (ws := [L34.wy17]) (hb := by decide) (wW := L34.w17)
      L34.ch5251_y17 L34.ch5251_s17 hc7.1
      (by rw [beq_iff_eq.1 L34.ch5251_o17, card_K₂,
        factorization_eq_one (n := 672) (m := 96) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)]; rfl)
      L34.ch5251_W17 (by decide) hc7.2 L34.ch5251_row17 x hxR hxo hxc

theorem star₃ :
    ∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₃ * x = x * r₃ →
      ∃ c ∈ C₃, (x * (c * x * c⁻¹)) ^ p ≠ 1 := by
  have hc3 := comm_of pkp_r3 L34.ch5251_c23
  have hc5 := comm_of pkp_r3 L34.ch5251_c25
  rintro p (rfl | rfl | rfl) x hxR hxo hxc
  · have := fact3
    exact row_packed (ws := [[1]]) (hb := by decide) (wW := L34.w23)
      L34.ch5251_y3 L34.ch5251_s3 hc3.1
      (by rw [beq_iff_eq.1 L34.ch5251_o3, card_K₃,
        factorization_eq_one (n := 240) (m := 80) Nat.prime_three (by norm_num) (by norm_num)
        (by norm_num)]; rfl)
      L34.ch5251_W23 (by decide) hc3.2 L34.ch5251_row23 x hxR hxo hxc
  · have := fact5
    exact row_packed (ws := [L34.wy25]) (hb := by decide) (wW := L34.w25)
      L34.ch5251_y25 L34.ch5251_s25 hc5.1
      (by rw [beq_iff_eq.1 L34.ch5251_o25, card_K₃,
        factorization_eq_one (n := 240) (m := 48) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)]; rfl)
      L34.ch5251_W25 (by decide) hc5.2 L34.ch5251_row25 x hxR hxo hxc
  · exact (no_elt (by rw [card_K₃]; norm_num) hxR hxo hxc).elim

theorem star₄ :
    ∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₄ * x = x * r₄ →
      (p = 3 ∧ x ∈ S) ∨ ∃ c ∈ C₄, (x * (c * x * c⁻¹)) ^ p ≠ 1 := by
  rintro p (rfl | rfl | rfl) x hxR hxo hxc
  · by_cases hxS : x ∈ S
    · exact Or.inl ⟨rfl, hxS⟩
    · exact Or.inr (fix_fact x hxR hxS (hxo ▸ pow_orderOf_eq_one x) hxc)
  · exact (no_elt (by rw [card_K₄]; norm_num) hxR hxo hxc).elim
  · exact (no_elt (by rw [card_K₄]; norm_num) hxR hxo hxc).elim

theorem factorization_72 : (72 : ℕ).factorization 3 = 2 := by
  have h : (72 : ℕ) = 3 ^ 2 * 8 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (by norm_num : Nat.Prime 3),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 8)]

theorem c0_fact :
    ∀ e ∈ C₄, orderOf e = 3 → ∃ c ∈ C₄, c * e * c⁻¹ ≠ e ∧ c * e * c⁻¹ * e ≠ 1 := by
  have := fact3
  have hqL : ∀ w ∈ L34.qGens, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 3 := by decide
  have hqc : ∀ s ∈ L34.qStrong, pkp s * r₄ = r₄ * pkp s := by
    rw [← pkp_r4]
    exact commOK_spec L34.ch5251_cq
  have hQ : (chainOf L34.qGens #v[0, 2] (by decide)).originalSubgroup ≤ C₄ :=
    chainOf_le fun w hw => Subgroup.mem_inf.2
      ⟨Subgroup.mem_centralizer_singleton_iff.2 (ev_comm L34.ch5251_qGens hqc w hw),
        ev_mem_S w (hqL w hw)⟩
  have hd4S : pkp Ivk8KBNorm.L34.d4 ∈ S := by
    rw [pkp_eq_of_val Ivk8KBNorm.L34.ch5250_d4]
    exact ev_mem_S Certificates.Ivk8KB.wordD4 (by decide)
  have hd4c : pkp Ivk8KBNorm.L34.d4 * r₄ = r₄ * pkp Ivk8KBNorm.L34.d4 := by
    rw [← pkp_r4]
    exact commOK_spec Ivk8KBNorm.L34.ch5250_d4Comm Ivk8KBNorm.L34.d4 (List.mem_singleton_self _)
  have hd4 : pkp Ivk8KBNorm.L34.d4 ∈ C₄ :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hd4c, hd4S⟩
  intro e he heo
  have he3 : e ^ 3 = 1 := heo ▸ pow_orderOf_eq_one e
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at heo
    omega
  obtain ⟨k, hk, hz⟩ := exists_conj_mem_of_card hQ
    (by rw [chainOf_card L34.ch5251_qGens L34.ch5251_sq, beq_iff_eq.1 L34.ch5251_oq,
      CFSG.ComponentClassification.PSL3Four.card_C₄, factorization_72]; rfl) he he3 he1
  have hz1 : k * e * k⁻¹ ≠ 1 := fun h => he1 (conj_eq_one_iff.1 h)
  obtain ⟨hn1, hn2⟩ := movesOK_spec L34.ch5251_moves _
    (chainOf_mem L34.ch5251_qGens L34.ch5251_sq hz) hz1
  have e1 : ∀ d : Equiv.Perm (Fin 42), d * (k * e * k⁻¹) * d⁻¹ =
      k * ((k⁻¹ * d * k) * e * (k⁻¹ * d * k)⁻¹) * k⁻¹ := fun d => by group
  refine ⟨k⁻¹ * pkp Ivk8KBNorm.L34.d4 * k, C₄.mul_mem (C₄.mul_mem (C₄.inv_mem hk) hd4) hk, ?_, ?_⟩
  · intro h
    apply hn1
    rw [e1, h]
  · intro h
    apply hn2
    rw [e1, eq_inv_of_mul_eq_one_left h]
    group

theorem star_facts :
    (∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₁ * x = x * r₁ →
      ∃ c ∈ C₁, (x * (c * x * c⁻¹)) ^ p ≠ 1) ∧
    (∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₂ * x = x * r₂ →
      ∃ c ∈ C₂, (x * (c * x * c⁻¹)) ^ p ≠ 1) ∧
    (∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₃ * x = x * r₃ →
      ∃ c ∈ C₃, (x * (c * x * c⁻¹)) ^ p ≠ 1) ∧
    (∀ p : ℕ, (p = 3 ∨ p = 5 ∨ p = 7) → ∀ x ∈ R, orderOf x = p → r₄ * x = x * r₄ →
      (p = 3 ∧ x ∈ S) ∨ ∃ c ∈ C₄, (x * (c * x * c⁻¹)) ^ p ≠ 1) ∧
    (∀ e ∈ C₄, orderOf e = 3 → ∃ c ∈ C₄, c * e * c⁻¹ ≠ e ∧ c * e * c⁻¹ * e ≠ 1) :=
  ⟨star₁, star₂, star₃, star₄, c0_fact⟩

end CFSG.KS.Ivk8KBStarV.Final

end
