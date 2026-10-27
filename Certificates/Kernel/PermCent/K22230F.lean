module

public import Certificates.Kernel.PermCent.K22230
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23U52Bridge
import all CFSG.Fischer.F4

public section

namespace CertificateChecks.KernelPermCent.U52

open CFSG.ComponentClassification.GSThmB.U52 CFSG.ComponentClassification.GSThmB.U52.Cover
open CFSG.KC.OrbGroup CFSG.KS.Raw.Orb CFSG.KC.Enum CFSG.KS CFSG.KC.ConjOrb CFSG.KC.LeftOrb
  CFSG.KC.BfsPin
open Matrix Subgroup CFSG.Assembly.LowTwoRank

noncomputable def suOf (k : ℕ) (hd : (matN k).det = 1)
    (hu : ((matN k).map (· ^ 2))ᵀ * matN k = 1) : StatedSU 5 2 CFSG.Fischer.F4 :=
  ⟨GeneralLinearGroup.mk'' (matN k) (by rw [hd]; exact isUnit_one),
    Subgroup.subset_closure ⟨hd, hu⟩⟩

theorem psi_suOf (k : ℕ) (hd : (matN k).det = 1) (hu : ((matN k).map (· ^ 2))ᵀ * matN k = 1)
    (i : Fin 341) :
    (psi (QuotientGroup.mk (suOf k hd hu)) i : ℕ) = ptIndex (mv5 (matN k) (decode i)) := by
  rw [psi_mk_apply, mulVec_eq_mv5]
  rfl

theorem psi_xElt (i : Fin 341) : (psi xElt i : ℕ) = ptIndex (mv5 (matN codeA) (decode i)) := by
  rw [← rep_tabA i, tabA, tabN_getElem!, mulVec_eq_mv5]

theorem psi_yElt (i : Fin 341) : (psi yElt i : ℕ) = ptIndex (mv5 (matN codeB) (decode i)) := by
  rw [← rep_tabB i, tabB, tabN_getElem!, mulVec_eq_mv5]

theorem prep_of_matOK {k p : ℕ} {g : Equiv.Perm (Fin 341)}
    (hg : ∀ i : Fin 341, (g i : ℕ) = ptIndex (mv5 (matN k) (decode i))) (h : matOK k p = true) :
    PRep 341 9 p g := by
  intro x
  rw [matOK, List.all_eq_true] at h
  rw [hg x]
  exact Nat.eq_of_beq_eq_true (h x (List.mem_range.2 x.2))

theorem detRA : (matN codeRA).det = 1 := by decide +kernel
theorem uniRA : ((matN codeRA).map (· ^ 2))ᵀ * matN codeRA = 1 := by decide +kernel
theorem detRB : (matN codeRB).det = 1 := by decide +kernel
theorem uniRB : ((matN codeRB).map (· ^ 2))ᵀ * matN codeRB = 1 := by decide +kernel
theorem detS0 : (matN 338775203954025).det = 1 := by decide +kernel
theorem uniS0 : ((matN 338775203954025).map (· ^ 2))ᵀ * matN 338775203954025 = 1 := by
  decide +kernel
theorem detS1 : (matN 89353621990077).det = 1 := by decide +kernel
theorem uniS1 : ((matN 89353621990077).map (· ^ 2))ᵀ * matN 89353621990077 = 1 := by
  decide +kernel
theorem detS2 : (matN 804734416917121).det = 1 := by decide +kernel
theorem uniS2 : ((matN 804734416917121).map (· ^ 2))ᵀ * matN 804734416917121 = 1 := by
  decide +kernel
theorem detS3 : (matN 783822959349761).det = 1 := by decide +kernel
theorem uniS3 : ((matN 783822959349761).map (· ^ 2))ᵀ * matN 783822959349761 = 1 := by
  decide +kernel

noncomputable def rAx : X₀ := QuotientGroup.mk (suOf codeRA detRA uniRA)

noncomputable def rBx : X₀ := QuotientGroup.mk (suOf codeRB detRB uniRB)

noncomputable def sylX : ℕ → X₀
  | 0 => QuotientGroup.mk (suOf 338775203954025 detS0 uniS0)
  | 1 => QuotientGroup.mk (suOf 89353621990077 detS1 uniS1)
  | 2 => QuotientGroup.mk (suOf 804734416917121 detS2 uniS2)
  | _ => QuotientGroup.mk (suOf 783822959349761 detS3 uniS3)

noncomputable def genX (k : ℕ) : X₀ := if k = 0 then xElt else yElt

theorem genX_image : genX '' {k | k < 2} = {xElt, yElt} := by
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (if_pos rfl)
    · exact Or.inr (if_neg (by norm_num))
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, if_pos rfl⟩
    · exact ⟨1, by norm_num, if_neg (by norm_num)⟩

theorem closure_genX : closure (genX '' {k | k < 2}) = ⊤ := by
  rw [genX_image]
  exact closure_xy

theorem prep_genX {G : ℕ → ℕ} (h0 : matOK codeA (G 0) = true) (h1 : matOK codeB (G 1) = true) :
    ∀ k < 2, PRep 341 9 (G k) (psi (genX k)) := by
  intro k hk
  interval_cases k
  · rw [genX, if_pos rfl]
    exact prep_of_matOK psi_xElt h0
  · rw [genX, if_neg (by norm_num)]
    exact prep_of_matOK psi_yElt h1

theorem baseL_lt : ∀ p ∈ baseL, p < 341 := by decide

theorem class_facts {N r : ℕ} {G GI T E D S : ℕ → ℕ} {rx : X₀}
    (hh : headK 341 9 2 G GI = true) (h0 : matOK codeA (G 0) = true)
    (h1 : matOK codeB (G 1) = true) (hcl : ∀ i < N, closPt 341 9 2 N G GI T E i = true)
    (htr : ∀ i < N, treePt 2 N r E D i = true) (hr : r < N) (ht : PRep 341 9 (T r) (psi rx))
    (hK : distinctK N (fun i => pkeyK 341 9 baseL (T i)) S = true) :
    N * Nat.card (centralizer ({rx} : Set X₀)) = 13685760 ∧
      ∀ y : X₀, (∃ i < N, PRep 341 9 (T i) (psi y)) → IsConj rx y := by
  obtain ⟨c, hc, hreach, hcl', hinj⟩ := conjOrb_reps (g := fun k => psi (genX k)) (t := psi rx)
    (by norm_num) hh (prep_genX h0 h1) hcl htr hr ht baseL_lt hK
  obtain ⟨hcard, hconj⟩ := class_of_reps psi psi_injective genX closure_genX rx c hreach hcl'
    ⟨r, hr, prep_eq (hc r hr) ht⟩ hinj
  refine ⟨hcard.trans card_X₀, fun y ⟨i, hi, hy⟩ => hconj y ⟨i, hi, prep_eq (hc i hi) hy⟩⟩

theorem binds_parts :
    matOK codeA (CA.G 0) = true ∧ matOK codeB (CA.G 1) = true ∧
    matOK codeA (CB.G 0) = true ∧ matOK codeB (CB.G 1) = true ∧
    matOK codeRA (CA.T CA.r0) = true ∧ matOK codeRB (CB.T CB.r0) = true ∧
    (∀ k < 4, matOK (sylCodes.getD k 0) (SH.G k) = true) ∧ SH.T 0 = pidn 341 9 ∧
    CA.N = 165 ∧ CB.N = 2970 ∧ SH.N = 1024 ∧ CA.r0 < 165 ∧ CB.r0 < 2970 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -, -, -, a15, a16⟩ := binds
  exact ⟨a1, a2, a3, a4, a5, a6, fun k hk => List.all_eq_true.1 a7 k (List.mem_range.2 hk),
    Nat.eq_of_beq_eq_true a8, a9, a10, a11, a15, a16⟩

theorem classA :
    Nat.card (centralizer ({rAx} : Set X₀)) = 82944 ∧
      ∀ y : X₀, (∃ i < 165, PRep 341 9 (CA.T i) (psi y)) → IsConj rAx y := by
  obtain ⟨a1, a2, -, -, a5, -, -, -, a9, -, -, a12, -⟩ := binds_parts
  have h := class_facts (N := CA.N) (rx := rAx) CA.h a1 a2
    (fun i hi => CA.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => CA.tr0 i (lt_of_lt_of_le hi (by decide))) (by omega)
    (prep_of_matOK (psi_suOf codeRA detRA uniRA) a5) CA.k
  rw [a9] at h
  exact ⟨by omega, h.2⟩

theorem classB :
    Nat.card (centralizer ({rBx} : Set X₀)) = 4608 ∧
      ∀ y : X₀, (∃ i < 2970, PRep 341 9 (CB.T i) (psi y)) → IsConj rBx y := by
  obtain ⟨-, -, a3, a4, -, a6, -, -, -, a10, -, -, a13⟩ := binds_parts
  have h := class_facts (N := CB.N) (rx := rBx) CB.h a3 a4
    (fun i hi => CB.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => CB.tr0 i (lt_of_lt_of_le hi (by decide))) (by omega)
    (prep_of_matOK (psi_suOf codeRB detRB uniRB) a6) CB.k
  rw [a10] at h
  exact ⟨by omega, h.2⟩

theorem prep_sylX : ∀ k < 4, PRep 341 9 (SH.G k) (psi (sylX k)) := by
  obtain ⟨-, -, -, -, -, -, a7, -⟩ := binds_parts
  intro k hk
  have h := a7 k hk
  interval_cases k
  · exact prep_of_matOK (psi_suOf _ _ _) h
  · exact prep_of_matOK (psi_suOf _ _ _) h
  · exact prep_of_matOK (psi_suOf _ _ _) h
  · exact prep_of_matOK (psi_suOf _ _ _) h

theorem sylow_facts :
    Nat.card (closure (sylX '' {k | k < 4})) = 1024 ∧
      ∀ y ∈ closure (sylX '' {k | k < 4}), ∃ i < 1024, PRep 341 9 (SH.T i) (psi y) := by
  obtain ⟨-, -, -, -, -, -, -, a8, -, -, a11, -⟩ := binds_parts
  have h0 : PRep 341 9 (SH.T 0) 1 := by
    rw [a8]
    exact prep_pidn (by norm_num) (by norm_num)
  obtain ⟨c, hc0, hc, hmem, hcl, hinj⟩ := leftOrb_reps (g := fun k => psi (sylX k))
    (N := SH.N) (by norm_num) prep_sylX (fun i hi => SH.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => SH.tr i (lt_of_lt_of_le hi (by decide))) (by omega) h0 baseL_lt SH.k
  obtain ⟨hcard, hall⟩ := group_of_reps psi psi_injective sylX c ⟨0, by omega, hc0⟩ hmem hcl hinj
  rw [a11] at hcard hall
  refine ⟨hcard, fun y hy => ?_⟩
  obtain ⟨i, hi, e⟩ := hall y hy
  exact ⟨i, hi, by rw [← e]; exact hc i (by omega)⟩

theorem coverK_spec {a b : Bool} {m : ℕ} (h : coverK a b m = true) :
    ∀ i < m, invol (SH.T i) = true → inClasses a b (SH.T i) = true := by
  intro i hi hv
  rw [coverK, List.all_eq_true] at h
  have := h i (List.mem_range.2 hi)
  rw [hv] at this
  simpa using this

theorem invol_of_prep {t : ℕ} {σ : Equiv.Perm (Fin 341)} (ht : PRep 341 9 t σ) (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) : invol t = true := by
  rw [invol, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun i hi => ?_, ?_⟩
  · have hi' := List.mem_range.1 hi
    have e1 : pg 9 (mask 9) t i = (σ ⟨i, hi'⟩ : ℕ) := ht ⟨i, hi'⟩
    rw [e1]
    have e := ht (σ ⟨i, hi'⟩)
    rw [e]
    have e2 : σ (σ ⟨i, hi'⟩) = ⟨i, hi'⟩ := by
      rw [← Equiv.Perm.mul_apply, h2, Equiv.Perm.one_apply]
    rw [e2]
    exact Nat.beq_refl i
  · cases e : Nat.beq t (pidn 341 9)
    · rfl
    · exfalso
      have he := Nat.eq_of_beq_eq_true e
      rw [he] at ht
      exact h1 (prep_eq ht (prep_pidn (by norm_num) (by norm_num)))

theorem inClasses_spec {t : ℕ} (h : inClasses true true t = true) :
    (∃ j < 165, CA.T j = t) ∨ ∃ j < 2970, CB.T j = t := by
  rw [inClasses, Bool.or_eq_true, Bool.true_and, Bool.true_and, List.any_eq_true,
    List.any_eq_true] at h
  rcases h with ⟨j, hj, e⟩ | ⟨j, hj, e⟩
  · exact Or.inl ⟨j, List.mem_range.1 hj, Nat.eq_of_beq_eq_true e⟩
  · exact Or.inr ⟨j, List.mem_range.1 hj, Nat.eq_of_beq_eq_true e⟩

theorem card_factorization : 2 ^ (Nat.card X₀).factorization 2 = 1024 := by
  rw [card_X₀, show (13685760 : ℕ) = 2 ^ 10 * 13365 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem card_centralizer_of_involution (x : X₀)
    (hx : orderOf x = 2) :
    Nat.card (centralizer ({x} : Set X₀)) = 82944 ∨
      Nat.card (centralizer ({x} : Set X₀)) = 4608 := by
  obtain ⟨hS, hSmem⟩ := sylow_facts
  have hpx : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx,
    pow_one])
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card (p := 2) (closure (sylX '' {k | k < 4}))
    (by rw [hS, card_factorization]) hpx
  obtain ⟨i, hi, hy⟩ := hSmem _ hg
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    rw [← sq]
    exact h
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hsq : psi (g⁻¹ * x * g) * psi (g⁻¹ * x * g) = 1 := by
    rw [← map_mul]
    have e : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [e, hx2, mul_one, inv_mul_cancel, map_one]
  have hne : psi (g⁻¹ * x * g) ≠ 1 := by
    intro e
    rw [← map_one psi] at e
    have e2 := psi_injective e
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [e2, mul_one, mul_inv_cancel]
  have hv := invol_of_prep hy hsq hne
  have hconjx : IsConj (g⁻¹ * x * g) x := isConj_iff.2 ⟨g, by group⟩
  rcases inClasses_spec (coverK_spec cover i hi hv) with ⟨j, hj, e⟩ | ⟨j, hj, e⟩
  · have hA := classA.2 _ ⟨j, hj, by rw [e]; exact hy⟩
    left
    rw [← card_centralizer_of_isConj (hA.trans hconjx), classA.1]
  · have hB := classB.2 _ ⟨j, hj, by rw [e]; exact hy⟩
    right
    rw [← card_centralizer_of_isConj (hB.trans hconjx), classB.1]

end CertificateChecks.KernelPermCent.U52

end
