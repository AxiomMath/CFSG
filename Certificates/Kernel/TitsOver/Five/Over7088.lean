module

public import CFSG.Quasithin.Recognition.RuRank3TitsCls
public import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroup

public section

namespace CertificateChecks.KernelTitsOver.Over7088

open CFSG.StandardType.TitsFive CFSG.StandardType.TitsOvergroup CFSG.StandardType.SylowPair
  CFSG.StandardType.SylowOvergroup CFSG.StandardType.TitsGenerators
  CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuRank3

theorem map_conj_map_conj (H : Subgroup (Equiv.Perm (Fin 1755))) (u v : Equiv.Perm (Fin 1755)) :
    (H.map (MulAut.conj u).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      H.map (MulAut.conj (v * u)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

@[expose] noncomputable def L : Subgroup (Equiv.Perm (Fin 1755)) := pairSide pairData titsS 0

@[expose] noncomputable def R : Subgroup (Equiv.Perm (Fin 1755)) := pairP pairData titsS

theorem map_conj_one (H : Subgroup (Equiv.Perm (Fin 1755))) :
    H.map (MulAut.conj (1 : Equiv.Perm (Fin 1755))).toMonoidHom = H := by
  ext x
  simp

theorem map_subtype_map_conj (H : Subgroup titsD) (g : titsD) :
    (H.map (MulAut.conj g).toMonoidHom).map titsD.subtype =
      (H.map titsD.subtype).map (MulAut.conj (g : Equiv.Perm (Fin 1755))).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem eq_map_conj_inv {H M : Subgroup (Equiv.Perm (Fin 1755))} {c : Equiv.Perm (Fin 1755)}
    (h : H = M.map (MulAut.conj c).toMonoidHom) : M = H.map (MulAut.conj c⁻¹).toMonoidHom := by
  rw [h, map_conj_map_conj, inv_mul_cancel, map_conj_one]

theorem parts : Sound pairData titsS ∧ pairCheck pairData = true ∧
    checkSideGen pairData sideGenWords = true := by
  have hc : titsFiveCheck () = true := Certificates.certificate465004
  obtain ⟨hpair, hsg, -, -⟩ := titsFiveCheck_parts hc
  exact ⟨sound_pairData (pairCheck_parts hpair).1, hpair, hsg⟩

theorem pairG_eq : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm

theorem card_L : Nat.card L = 7800 := by
  obtain ⟨hS, hpair, -⟩ := parts
  exact card_pairSide hS (pairCheck_parts hpair).2.2.2.2.1 (k := 0) (by simp [pairData])

theorem eq_conj_of_pairP_le {Y : Subgroup (Equiv.Perm (Fin 1755))}
    (hPY : R ≤ Y) (hYD : Y ≤ titsD) (hY : Y ≠ titsD)
    (hN : ¬ Nat.card Y ∣ 1200) :
    ∃ a ∈ titsD, Y = L.map (MulAut.conj a).toMonoidHom := by
  have hc : titsFiveCheck () = true := Certificates.certificate465004
  obtain ⟨hS, hpair, hsg⟩ := parts
  obtain ⟨-, -, hN', -, -, hCover, -, -⟩ := pairCheck_parts hpair
  have hG := pairG_eq
  by_cases hYN : Y ≤ pairN pairData titsS
  · exfalso
    apply hN
    have h : Nat.card Y ∣ pairData.nOrder :=
      (Subgroup.card_dvd_of_le hYN).trans (dvd_of_eq (card_pairN hS hN'))
    have e : pairData.nOrder = 1200 := by norm_num [pairData]
    rwa [e] at h
  obtain ⟨y, hyY, hyN⟩ := Set.not_subset.1 hYN
  rcases dichotomy hS hpair hPY (hYD.trans (le_of_eq hG.symm)) (fun h => hY (h.trans hG)) hyY
    with h | ⟨i, hi, hk, -, a, ha, hle⟩
  · exact absurd h hyN
  have key : ∀ i < 24, pairData.kind[i]! ≠ 0 → i = 23 := by decide
  have hlen24 : pairData.repW.length = 24 := rfl
  have hi23 : i = 23 := key i (by omega) hk
  subst hi23
  have hL : pairSide pairData titsS 0 ≤
      pairClosure (pairP pairData titsS) ((pairReps pairData titsS).getD (23 + 1) 1) :=
    pairSide_le_pairClosure hS (invsOK_of_checkCover hCover) hsg (i := 23) (k := 0) hi
      (by show pairData.kind[23]! = 0 + 1; decide)
  have hLY : L.map (MulAut.conj a).toMonoidHom ≤ Y :=
    (Subgroup.map_mono hL).trans hle
  have haG : a ∈ titsD := (le_of_eq hG) (pairN_le_pairG ha)
  exact ⟨a, haG, eq_map_conj_of_maximal haG (pairSide_maximal hc) hLY hYD hY⟩

theorem eq_conj_of_card {Y : Subgroup (Equiv.Perm (Fin 1755))} (hYD : Y ≤ titsD)
    (h25 : 25 ∣ Nat.card Y) (hY : Y ≠ titsD) (hN : ¬ Nat.card Y ∣ 1200) :
    ∃ a ∈ titsD, Y = L.map (MulAut.conj a).toMonoidHom := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hS, hpair, -⟩ := parts
  have hP := (pairCheck_parts hpair).2.1
  have hPD : R ≤ titsD := fun x hx => pairG_eq ▸ pairP_le_pairG hx
  have hP25 : Nat.card R = 5 ^ 2 := (card_pairP hS hP).trans rfl
  have hD : Nat.card titsD = 5 ^ 2 * 718848 := card_titsD.trans (by norm_num)
  let S : Sylow 5 titsD := Sylow.ofCard (R.subgroupOf titsD) (by
    rw [card_subgroupOf_of_le hPD, hP25]
    exact card_eq_pow_factorization hD (by norm_num))
  have hSc : (S : Subgroup titsD) = R.subgroupOf titsD := Sylow.coe_ofCard _ _
  have hinv : ∀ (g : titsD) (X : Subgroup titsD),
      (¬ Nat.card (X.map (MulAut.conj g).toMonoidHom) ∣ 1200 → ∃ a ∈ titsD,
        (X.map (MulAut.conj g).toMonoidHom).map titsD.subtype =
          L.map (MulAut.conj a).toMonoidHom) →
      (¬ Nat.card X ∣ 1200 → ∃ a ∈ titsD, X.map titsD.subtype =
          L.map (MulAut.conj a).toMonoidHom) := by
    intro g X hX hXN
    have hcard : Nat.card (X.map (MulAut.conj g).toMonoidHom) = Nat.card X :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    obtain ⟨a, ha, he⟩ := hX (by rwa [hcard])
    refine ⟨(g : Equiv.Perm (Fin 1755))⁻¹ * a, mul_mem (inv_mem g.2) ha, ?_⟩
    rw [map_subtype_map_conj] at he
    rw [eq_map_conj_inv he, map_conj_map_conj, mul_inv_cancel_right, map_conj_map_conj,
      inv_mul_cancel, map_conj_one]
  have hbase : ∀ X : Subgroup titsD, (S : Subgroup titsD) ≤ X → X ≠ ⊤ →
      (¬ Nat.card X ∣ 1200 → ∃ a ∈ titsD, X.map titsD.subtype =
          L.map (MulAut.conj a).toMonoidHom) := by
    intro X hSX hXtop hXN
    have hPX : R ≤ X.map titsD.subtype := by
      intro x hx
      refine ⟨⟨x, hPD hx⟩, hSX ?_, rfl⟩
      rw [hSc]
      exact hx
    have hne : X.map titsD.subtype ≠ titsD := by
      intro heq
      apply hXtop
      have htop : (⊤ : Subgroup titsD).map titsD.subtype = titsD := by
        rw [Subgroup.map_top titsD.subtype, Subgroup.range_subtype]
      exact (Subgroup.map_subtype_inj (H := titsD)).mp (heq.trans htop.symm)
    have hcard : Nat.card (X.map titsD.subtype) = Nat.card X :=
      Subgroup.card_map_of_injective titsD.subtype_injective
    exact eq_conj_of_pairP_le hPX (Subgroup.map_subtype_le X) hne (by rwa [hcard])
  have hcY : Nat.card (Y.subgroupOf titsD) = Nat.card Y := card_subgroupOf_of_le hYD
  have hne : Y.subgroupOf titsD ≠ ⊤ := by
    intro h
    apply hY
    refine le_antisymm hYD fun x hx => ?_
    have hx' : (⟨x, hx⟩ : titsD) ∈ Y.subgroupOf titsD := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hx'
  have hidx : ¬ 5 ∣ (Y.subgroupOf titsD).index := by
    have hm := Subgroup.card_mul_index (Y.subgroupOf titsD)
    rw [hcY, card_titsD] at hm
    obtain ⟨m, hm'⟩ := h25
    rintro ⟨j, hj⟩
    rw [hm', hj] at hm
    have h125 : 125 ∣ 17971200 := ⟨m * j, by rw [← hm]; ring⟩
    norm_num at h125
  obtain ⟨a, ha, he⟩ := forall_of_sylow_le S _ hinv hbase hne hidx (by rwa [hcY])
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hYD] at he
  exact ⟨a, ha, he⟩

theorem mem_titsD_of_pow_odd {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsA) {k : ℕ}
    (hk : x ^ (2 * k + 1) = 1) : x ∈ titsD := by
  have hk' : (⟨x, hx⟩ : titsA) ^ (2 * k + 1) = 1 := Subtype.ext (by simp [hk])
  have h2 := Subgroup.mul_self_mem_of_index_two titsD_index ⟨x, hx⟩
  have h3 := pow_mem h2 (k + 1)
  have e : ((⟨x, hx⟩ : titsA) * ⟨x, hx⟩) ^ (k + 1) = ⟨x, hx⟩ := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hk', one_mul]
  rw [e, Subgroup.mem_subgroupOf] at h3
  exact h3


theorem card_titsD_lt : ¬ Nat.card titsD ≤ 7800 := by
  rw [card_titsD]
  norm_num

theorem dvd_card_inf : 25 ∣ Nat.card ↥(titsK0 ⊓ titsD) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨X, hX⟩ := Sylow.exists_subgroup_card_pow_prime 5 (n := 2) (G := titsK0)
    (by rw [card_titsK0]; norm_num)
  have hle : X.map titsK0.subtype ≤ titsK0 ⊓ titsD := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 : (⟨y, hy⟩ : X) ^ 25 = 1 := by
      have := pow_card_eq_one' (G := X) (x := ⟨y, hy⟩)
      rwa [hX] at this
    have h2 : ((y : titsK0) : Equiv.Perm (Fin 1755)) ^ (2 * 12 + 1) = 1 := by
      have := congrArg (fun z : X => ((z : titsK0) : Equiv.Perm (Fin 1755))) h1
      simpa using this
    exact mem_titsD_of_pow_odd (titsK0_le y.2) h2
  have h := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective titsK0.subtype_injective, hX] at h

theorem dvd13_card_inf : 13 ∣ Nat.card ↥(titsK0 ⊓ titsD) := by
  have hD : titsX13 ∈ titsD := mem_titsD_of_pow_odd titsX13_mem (k := 6) titsX13_pow
  have h := orderOf_dvd_natCard (⟨titsX13, titsX13_mem_K0, hD⟩ : ↥(titsK0 ⊓ titsD))
  have e : orderOf (⟨titsX13, titsX13_mem_K0, hD⟩ : ↥(titsK0 ⊓ titsD)) = 13 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_titsX13
  rwa [e] at h

theorem titsK0_eq_conj : titsK0 ≤ titsD ∧
    ∃ c ∈ titsD, titsK0 = L.map (MulAut.conj c).toMonoidHom := by
  have hT := eq_conj_of_card (Y := titsK0 ⊓ titsD) inf_le_right dvd_card_inf
    (fun h => card_titsD_lt (by
      rw [← h, ← card_titsK0]
      exact Subgroup.card_le_of_le inf_le_left))
    (fun h => absurd (dvd13_card_inf.trans h) (by norm_num))
  obtain ⟨b, -, hb⟩ := hT
  have hcard : Nat.card ↥(titsK0 ⊓ titsD) = 7800 := by
    rw [hb, Subgroup.card_map_of_injective (MulAut.conj b).injective, card_L]
  have hK0 : titsK0 ⊓ titsD = titsK0 :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, card_titsK0])
  have hKD : titsK0 ≤ titsD := hK0 ▸ inf_le_right
  refine ⟨hKD, eq_conj_of_card hKD (by rw [card_titsK0]; norm_num)
    (fun h => card_titsD_lt (by rw [← h, card_titsK0])) (by rw [card_titsK0]; norm_num)⟩

open Certificates in
open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuRank3 in
theorem c7088 : ∀ K : Subgroup (Equiv.Perm (Fin 1755)), K ≤ titsD → 25 ∣ Nat.card K →
    7800 ≤ Nat.card K → K ≠ titsD → ∃ d ∈ titsD, K = titsK0.map (MulAut.conj d).toMonoidHom := by
  refine fun K hKD h25 h7800 hK => ?_
  obtain ⟨a, ha, hKa⟩ := eq_conj_of_card hKD h25 hK fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  obtain ⟨-, c, hc, hK0⟩ := titsK0_eq_conj
  refine ⟨a * c⁻¹, mul_mem ha (inv_mem hc), ?_⟩
  rw [hKa, eq_map_conj_inv hK0, map_conj_map_conj]

end CertificateChecks.KernelTitsOver.Over7088

end
