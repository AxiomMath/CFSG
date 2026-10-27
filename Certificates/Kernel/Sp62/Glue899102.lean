module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
public import Certificates.Data.RudvalisFF81Sp6Basis
public import Certificates.Kernel.Sp62.Final
public import Certificates.Kernel.Sp62.Cen899102

public section

namespace CFSG.KD.Sp62.T899102

open CFSG.KC.Sp62 CFSG.KD.Sp62 CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit
  CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

@[expose] def gC : Fin 5 → List ℕ :=
  ![p01C, p12C, fl0C, CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv.s0C, fl2C]

theorem gC_pairT : ∀ i : Fin 5, pairT (gC i, gC i) = true := by decide +kernel

theorem gC_pair (i : Fin 5) : pairCheck (gC i, gC i) = true := pairCheck_of (gC_pairT i)

theorem canon_gC (i : Fin 5) : canon6 (gC i) = true := (pairCheck_spec (gC_pair i)).1

@[expose] noncomputable def nH (i : Fin 5) : H6 := ofCode (gC i, gC i) (gC_pair i)

theorem mat6_nH (i : Fin 5) : mat6 (nH i) = dec6 (gC i) := mat6_ofCode _ _

theorem mat6_nH_inv (i : Fin 5) : mat6 (nH i)⁻¹ = dec6 (gC i) := mat6_ofCode_inv _ _

@[expose] noncomputable def wordH (w : List (Fin 5)) : H6 := (w.map nH).prod

@[expose] def conjL (w : List (Fin 5)) (c : List ℕ) : List ℕ :=
  w.foldr (fun i acc => mul6 (mul6 (gC i) acc) (gC i)) c

@[expose] noncomputable def conjN (w : List (Fin 5)) (X : ℕ) : ℕ :=
  w.foldr (fun i acc => MULF (MULF (pk (gC i)) acc) (pk (gC i))) X

theorem conjL_cons (i : Fin 5) (w : List (Fin 5)) (c : List ℕ) :
    conjL (i :: w) c = mul6 (mul6 (gC i) (conjL w c)) (gC i) := rfl

theorem mat6_conj_word {x : H6} {c : List ℕ} (h : mat6 x = dec6 c) :
    ∀ w : List (Fin 5), mat6 (wordH w * x * (wordH w)⁻¹) = dec6 (conjL w c)
  | [] => by
    rw [wordH, List.map_nil, List.prod_nil, one_mul, inv_one, mul_one, h]
    rfl
  | i :: w => by
    have e : wordH (i :: w) * x * (wordH (i :: w))⁻¹ =
        nH i * (wordH w * x * (wordH w)⁻¹) * (nH i)⁻¹ := by
      simp only [wordH, List.map_cons, List.prod_cons]
      group
    rw [e, map_mul, map_mul, mat6_conj_word h w, mat6_nH, mat6_nH_inv, conjL_cons, dec6_mul6,
      dec6_mul6]

theorem conjW_pk {c : List ℕ} {X : ℕ} (h : canon6 c = true ∧ pk c = X) :
    ∀ w : List (Fin 5), canon6 (conjL w c) = true ∧ pk (conjL w c) = conjN w X
  | [] => h
  | i :: w => mulE (mulE ⟨canon_gC i, rfl⟩ (conjW_pk h w)) ⟨canon_gC i, rfl⟩

theorem conj_eq {x y : H6} {c d : List ℕ} (hx : mat6 x = dec6 c) (hy : mat6 y = dec6 d)
    (hc : canon6 c = true) (hd : canon6 d = true) (w : List (Fin 5))
    (hn : conjN w (pk c) = pk d) : wordH w * x * (wordH w)⁻¹ = y := by
  apply mat6_injective
  have h1 := conjW_pk ⟨hc, rfl⟩ w
  rw [mat6_conj_word hx w, hy, pk_inj h1.1 hd (h1.2.trans hn)]

@[expose] def wd2 (a b c : ℕ) : List (Fin 5) :=
  if c = 0 then (if a = 2 then [2] else []) ++ (if b = 2 then [3] else [])
  else if b = 0 then (if a = 2 then [2] else []) ++ (if c = 2 then [4] else []) ++ [1]
  else (if b = 2 then [3] else []) ++ (if c = 2 then [4] else []) ++ [0, 1]

@[expose] def wd3 (a b c : ℕ) : List (Fin 5) :=
  (if a = 2 then [2] else []) ++ (if b = 2 then [3] else []) ++ (if c = 2 then [4] else [])

theorem wt2_num : ∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 2 →
    conjN (wd2 a b c) (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 1 1 0) =
      VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) a b c := by
  decide +kernel

theorem wt3_num : ∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 3 →
    conjN (wd3 a b c) (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 1 1 1) =
      VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) a b c := by
  decide +kernel

theorem pk_z0 : pk (zCode 0) = REC 27 := (z_ok 0).1.2
theorem pk_z1 : pk (zCode 1) = REC 28 := (z_ok 1).1.2
theorem pk_z2 : pk (zCode 2) = REC 29 := (z_ok 2).1.2

theorem commutes6_pk {c : List ℕ} (hc : canon6 c = true) (i : Fin 3) :
    commutes6 c (zCode i) =
      Nat.beq (MULF (pk c) (pk (zCode i))) (MULF (pk (zCode i)) (pk c)) := by
  unfold commutes6
  rw [beq_pk (canon6_mul6 _ _) (canon6_mul6 _ _), pk_mul6 hc (zc_ok i), pk_mul6 (zc_ok i) hc]

theorem swap01 : wordH [0] * zH 0 * (wordH [0])⁻¹ = zH 1 ∧
    wordH [0] * zH 1 * (wordH [0])⁻¹ = zH 0 ∧ wordH [0] * zH 2 * (wordH [0])⁻¹ = zH 2 :=
  ⟨conj_eq (mat6_zH 0) (mat6_zH 1) (zc_ok 0) (zc_ok 1) [0] (by decide +kernel),
    conj_eq (mat6_zH 1) (mat6_zH 0) (zc_ok 1) (zc_ok 0) [0] (by decide +kernel),
    conj_eq (mat6_zH 2) (mat6_zH 2) (zc_ok 2) (zc_ok 2) [0] (by decide +kernel)⟩

theorem swap12 : wordH [1] * zH 0 * (wordH [1])⁻¹ = zH 0 ∧
    wordH [1] * zH 1 * (wordH [1])⁻¹ = zH 2 ∧ wordH [1] * zH 2 * (wordH [1])⁻¹ = zH 1 :=
  ⟨conj_eq (mat6_zH 0) (mat6_zH 0) (zc_ok 0) (zc_ok 0) [1] (by decide +kernel),
    conj_eq (mat6_zH 1) (mat6_zH 2) (zc_ok 1) (zc_ok 2) [1] (by decide +kernel),
    conj_eq (mat6_zH 2) (mat6_zH 1) (zc_ok 2) (zc_ok 1) [1] (by decide +kernel)⟩

theorem mat6_z01 : mat6 (zH 0 * zH 1) = dec6 (vecCode 1 1 0) := by
  have h := mat6_pow_mul 1 1 0
  rwa [pow_one, pow_one, pow_zero, mul_one] at h

theorem mat6_z012 : mat6 (zH 0 * zH 1 * zH 2) = dec6 (vecCode 1 1 1) := by
  have h := mat6_pow_mul 1 1 1
  rwa [pow_one, pow_one, pow_one] at h

theorem wt2 : ∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 2 →
    ∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c = g * (zH 0 * zH 1) * g⁻¹ := by
  intro a ha b hb c hc h
  refine ⟨wordH (wd2 a b c), (conj_eq mat6_z01 (mat6_pow_mul a b c) (canon6_vecCode _ _ _)
    (canon6_vecCode _ _ _) _ ?_).symm⟩
  rw [(vecCode_pk zc_ok 1 1 0).2, (vecCode_pk zc_ok a b c).2]
  exact wt2_num a ha b hb c hc h

theorem wt3 : ∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 3 →
    ∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c = g * (zH 0 * zH 1 * zH 2) * g⁻¹ := by
  intro a ha b hb c hc h
  refine ⟨wordH (wd3 a b c), (conj_eq mat6_z012 (mat6_pow_mul a b c) (canon6_vecCode _ _ _)
    (canon6_vecCode _ _ _) _ ?_).symm⟩
  rw [(vecCode_pk zc_ok 1 1 1).2, (vecCode_pk zc_ok a b c).2]
  exact wt3_num a ha b hb c hc h

theorem aElt_zero : aElt 0 = zH 0 := by
  simp only [aElt, aVec, vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    pow_zero, mul_one, mul_one]

theorem mem_baseA_of_commute {x : H6} (hc : ∀ i, x * zH i = zH i * x) : x ∈ baseA zH := by
  have hmem : x ∈ centSub 0 := by
    rw [centSub_eq, aElt_zero, Subgroup.mem_centralizer_singleton_iff]
    exact hc 0
  obtain ⟨t, ht, hct, hcan⟩ := exists_code_closure (centGens 0) (pairs_spec.2.2.2 0) _
    (cent_spec 0).2.1 hmem
  have hsz : (closureT ((centGens 0).map Prod.fst)).size = 2160 := by
    have h := (clos_ok 0).1
    simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.1
  have ht' : t < 2160 := hsz ▸ ht
  have hpk : pk ((closureT ((centGens 0).map Prod.fst)).getD t []) = recX REC 38 t :=
    ((clos_ok 0).2 t ht').2
  have h1 := commutes6_of_commute hct.symm (mat6_zH 1) (hc 1)
  have h2 := commutes6_of_commute hct.symm (mat6_zH 2) (hc 2)
  rw [commutes6_pk hcan, hpk, pk_z1] at h1
  rw [commutes6_pk hcan, hpk, pk_z2] at h2
  have hcen : cenF (REC 27) (REC 28) (REC 29) (recX REC 38 t) = true :=
    CFSG.KC.G2Three.allBelow_g2 cen899102_ok (by norm_num) t ht'
  rw [cenF, h1, h2, Bool.and_self, Bool.not_true, Bool.false_or] at hcen
  simp only [inA0, List.any_eq_true, List.mem_range, Nat.beq_eq] at hcen
  obtain ⟨a, -, b, -, c, -, e⟩ := hcen
  have hv := vecCode_pk zc_ok a b c
  rw [pk_z0, pk_z1, pk_z2] at hv
  have hcode : (closureT ((centGens 0).map Prod.fst)).getD t [] = vecCode a b c :=
    pk_inj hcan hv.1 (by rw [hpk, e, hv.2])
  have hx : x = zH 0 ^ a * zH 1 ^ b * zH 2 ^ c :=
    mat6_injective (by rw [← hct, hcode, mat6_pow_mul])
  rw [hx]
  exact mul_mem (mul_mem (pow_mem (z_mem_baseA 0) _) (pow_mem (z_mem_baseA 1) _))
    (pow_mem (z_mem_baseA 2) _)

theorem cen_baseA : Subgroup.centralizer (baseA zH : Set H6) = baseA zH := by
  refine le_antisymm (fun x hx => mem_baseA_of_commute fun i => ?_) (fun x hx => ?_)
  · exact (Subgroup.mem_centralizer_iff.mp hx (zH i) (z_mem_baseA i)).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨u, rfl⟩ := (mem_baseA_iff wreathFacts_zH).mp hy
    obtain ⟨v, rfl⟩ := (mem_baseA_iff wreathFacts_zH).mp hx
    rw [← vecElt_add wreathFacts_zH, ← vecElt_add wreathFacts_zH, add_comm]

end CFSG.KD.Sp62.T899102

namespace CFSG.KD.Sp62

open CFSG.KD.Sp62.T899102

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.RankThree.PartTwo.Sec4.Item434Kit in
open Certificates in
theorem gen899102_holds : 
    (∃ p : H6, p * zH 0 * p⁻¹ = zH 1 ∧ p * zH 1 * p⁻¹ = zH 0 ∧ p * zH 2 * p⁻¹ = zH 2) ∧
    (∃ p : H6, p * zH 0 * p⁻¹ = zH 0 ∧ p * zH 1 * p⁻¹ = zH 2 ∧ p * zH 2 * p⁻¹ = zH 1) ∧
    Subgroup.centralizer (baseA zH : Set H6) = baseA zH ∧
    (∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 2 →
      ∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c = g * (zH 0 * zH 1) * g⁻¹) ∧
    (∀ a < 3, ∀ b < 3, ∀ c < 3, ([a, b, c].filter (· != 0)).length = 3 →
      ∃ g : H6, zH 0 ^ a * zH 1 ^ b * zH 2 ^ c = g * (zH 0 * zH 1 * zH 2) * g⁻¹) :=
  ⟨⟨wordH [0], swap01⟩, ⟨wordH [1], swap12⟩, cen_baseA, wt2, wt3⟩

end CFSG.KD.Sp62

end
