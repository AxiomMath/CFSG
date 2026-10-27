module

public import Certificates.Kernel.Sporadic.Fi24P7.Pt
import Certificates.Kernel.Sporadic.Fi24P7.Spec
import Certificates.Kernel.Sporadic.Fi24P7.MC
import Certificates.Kernel.Sporadic.Fi24P7.S02
import Certificates.Kernel.Sporadic.Fi24P7.S1
import Certificates.Kernel.Sporadic.Fi24P7.S3
import Certificates.Kernel.Sporadic.Fi24P7.S4
import Mathlib.Tactic.FinCases

public section

namespace CertificateChecks.KernelFi24P7

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 CertificateChecks.KernelFi24Fix
  CertificateChecks.KernelFi24Orb CertificateChecks.KernelFi24G2e CertificateChecks.KernelFi24Ext
  CertificateChecks.KernelFi24F3d CFSG.KC.Fi24FixK CFSG.KC.Fi24P7S CFSG.KC.Fi24P7 CFSG.Sporadic.Fi24
  CFSG.KD.Fi24G2e CFSG.KD.Fi24P7

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24G2e.BX CFSG.KD.Fi24P7.MX CFSG.KD.BrFi24.ONE
  CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24P7.TB

theorem lt12 : ∀ w ∈ [J.S0, J.S1, J.S2, J.S3, J.S4, J.A0, J.B0, J.A2, J.T2, J.A4, J.B4],
    ∀ g ∈ w, g < 12 := by decide +kernel

theorem S0_lt : ∀ g ∈ J.S0, g < 12 := lt12 _ (by simp)
theorem S1_lt : ∀ g ∈ J.S1, g < 12 := lt12 _ (by simp)
theorem S2_lt : ∀ g ∈ J.S2, g < 12 := lt12 _ (by simp)
theorem S3_lt : ∀ g ∈ J.S3, g < 12 := lt12 _ (by simp)
theorem S4_lt : ∀ g ∈ J.S4, g < 12 := lt12 _ (by simp)
theorem A0_lt : ∀ g ∈ J.A0, g < 12 := lt12 _ (by simp)
theorem B0_lt : ∀ g ∈ J.B0, g < 12 := lt12 _ (by simp)
theorem A2_lt : ∀ g ∈ J.A2, g < 12 := lt12 _ (by simp)
theorem T2_lt : ∀ g ∈ J.T2, g < 12 := lt12 _ (by simp)
theorem A4_lt : ∀ g ∈ J.A4, g < 12 := lt12 _ (by simp)
theorem B4_lt : ∀ g ∈ J.B4, g < 12 := lt12 _ (by simp)

theorem B2_lt : ∀ g ∈ B2, g < 12 := by
  intro g hg
  simp only [B2, List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact T2_lt g h
  · exact A2_lt g h
  · exact T2_lt g h

theorem even : ∀ w ∈ [J.S0, J.S1, J.S2, J.S3, J.S4, J.A0, J.B0, J.A2, J.A4, J.B4, B2],
    w.length % 2 = 0 := by decide +kernel

theorem T2_eq : J.T2 = [2] := by decide +kernel

theorem A2_eq : J.A2 = J.CA2.flatten := by decide +kernel
theorem A4_eq : J.A4 = J.CA4.flatten := by decide +kernel
theorem B4_eq : J.B4 = J.CB4.flatten := by decide +kernel
theorem S4_eq : J.S4 = J.CS4.flatten := by decide +kernel

theorem lens : J.CA2.length = 10 ∧ J.CA4.length = 11 ∧ J.CB4.length = 11 ∧ J.CS4.length = 5 := by
  decide +kernel

theorem pieces_lt {w : List ℕ} {P : List (List ℕ)} (e : w = P.flatten) (hw : ∀ g ∈ w, g < 12) :
    ∀ p ∈ P, ∀ g ∈ p, g < 12 := fun p hp g hg => hw g (by rw [e]; exact List.mem_flatten.2 ⟨p, hp, hg⟩)

theorem mat_A2 : Cn (CFSG.KD.Fi24P7.MX 0) ∧
    ((xw J.A2 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (CFSG.KD.Fi24P7.MX 0) := by
  rw [A2_eq]
  exact chain_mat (by norm_num) lens.1 (pieces_lt A2_eq A2_lt) CA2.all

theorem mat_A4 : Cn (CFSG.KD.Fi24P7.MX 10) ∧
    ((xw J.A4 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (CFSG.KD.Fi24P7.MX 10) := by
  rw [A4_eq]
  exact chain_mat (by norm_num) lens.2.1 (pieces_lt A4_eq A4_lt) CA4.all

theorem mat_B4 : Cn (CFSG.KD.Fi24P7.MX 21) ∧
    ((xw J.B4 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (CFSG.KD.Fi24P7.MX 21) := by
  rw [B4_eq]
  exact chain_mat (by norm_num) lens.2.2.1 (pieces_lt B4_eq B4_lt) CB4.all

theorem mat_S4 : Cn (CFSG.KD.Fi24P7.MX 32) ∧
    ((xw J.S4 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (CFSG.KD.Fi24P7.MX 32) := by
  rw [S4_eq]
  exact chain_mat (by norm_num) lens.2.2.2 (pieces_lt S4_eq S4_lt) CS4.all

noncomputable abbrev sE : Fin 5 → GL (Fin 781) (ZMod 3) := ![xw J.S0, xw J.S1, xw J.S2, xw J.S3, xw J.S4]

theorem pow3_of_word {w : List ℕ} (hw : ∀ g ∈ w, g < 12)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (w ++ w ++ w) CFSG.KD.BrFi24.ONE)
      CFSG.KD.BrFi24.ONE = true) : xw w ^ 3 = 1 := by
  have h1 := xw_one_beq (u := w ++ w ++ w) (fun g hg => by
    simp only [List.mem_append] at hg
    rcases hg with (h | h) | h <;> exact hw g h) h
  rw [xw_append, xw_append] at h1
  rw [← h1]
  simp only [pow_succ, pow_zero, one_mul]

theorem s4_pow3 : xw J.S4 ^ 3 = 1 := pow3_of_mat mat_S4.1 mat_S4.2 MS.z3

theorem card0 : Nat.card (ptFix (xw J.S0)) = 3240 := by
  rw [card_ptFix_xw S0_lt, card_fix_okS S0.all]
  decide +kernel

theorem card1 : Nat.card (ptFix (xw J.S1)) = 1485 := by
  rw [card_ptFix_xw S1_lt, card_fix_okS S1.all]
  decide +kernel

theorem card2 : Nat.card (ptFix (xw J.S2)) = 378 := by
  rw [card_ptFix_xw S2_lt, card_fix_okS S2.all]
  decide +kernel

theorem card3 : Nat.card (ptFix (xw J.S3)) = 162 := by
  rw [card_ptFix_xw S3_lt, card_fix_okS S3.all]
  decide +kernel

theorem card4 : Nat.card (ptFix (xw J.S4)) = 0 := by
  rw [card_ptFix_xw S4_lt, card_fix_okS S4.all]
  decide +kernel

theorem ne_of_card {w : List ℕ} (hw : ∀ g ∈ w, g < 12) {c : ℕ} (hc : Nat.card (ptFix (xw w)) = c)
    (hne : c ≠ 306936) : xw w ≠ 1 := by
  refine xw_ne_one hw ?_
  rw [← card_ptFix_xw hw, hc]
  exact hne

theorem s_facts (i : Fin 5) : sE i ∈ seedGrp ∧ sE i ^ 3 = 1 ∧ sE i ≠ 1 := by
  fin_cases i
  · exact ⟨xw_mem S0_lt (even _ (by simp)), pow3_of_word S0_lt MS.s0, ne_of_card S0_lt card0 (by norm_num)⟩
  · exact ⟨xw_mem S1_lt (even _ (by simp)), pow3_of_word S1_lt MS.s1, ne_of_card S1_lt card1 (by norm_num)⟩
  · exact ⟨xw_mem S2_lt (even _ (by simp)), pow3_of_word S2_lt MS.s2, ne_of_card S2_lt card2 (by norm_num)⟩
  · exact ⟨xw_mem S3_lt (even _ (by simp)), pow3_of_word S3_lt MS.s3, ne_of_card S3_lt card3 (by norm_num)⟩
  · exact ⟨xw_mem S4_lt (even _ (by simp)), s4_pow3, ne_of_card S4_lt card4 (by norm_num)⟩

theorem order7 {a b : GL (Fin 781) (ZMod 3)} (ha : a ^ 7 = 1) (hb : b ^ 7 = 1)
    (h81 : 81 ∣ Nat.card (Subgroup.closure ({a, b} : Set (GL (Fin 781) (ZMod 3))))) :
    orderOf a = 7 ∧ orderOf b = 7 := by
  have hp : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have one : ∀ {x y : GL (Fin 781) (ZMod 3)}, y ^ 7 = 1 →
      81 ∣ Nat.card (Subgroup.closure ({x, y} : Set (GL (Fin 781) (ZMod 3)))) → x ≠ 1 := by
    intro x y hy h hx
    rw [hx] at h
    have e : Subgroup.closure ({1, y} : Set (GL (Fin 781) (ZMod 3))) = Subgroup.zpowers y := by
      rw [Subgroup.zpowers_eq_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact Subgroup.one_mem _
        · exact Subgroup.subset_closure rfl
      · exact Subgroup.closure_mono (Set.subset_insert _ _)
    rw [e, Nat.card_zpowers] at h
    have h7 := orderOf_dvd_of_pow_eq_one hy
    have := Nat.dvd_trans h h7
    norm_num at this
  have hb' : b ≠ 1 := by
    refine one ha ?_
    rwa [Set.pair_comm]
  exact ⟨orderOf_eq_prime ha (one hb h81), orderOf_eq_prime hb hb'⟩

theorem pow7_of_word {w : List ℕ} (hw : ∀ g ∈ w, g < 12)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (w ++ w ++ w ++ w ++ w ++ w ++ w)
      CFSG.KD.BrFi24.ONE) CFSG.KD.BrFi24.ONE = true) : xw w ^ 7 = 1 := by
  have h1 := xw_one_beq (u := w ++ w ++ w ++ w ++ w ++ w ++ w) (fun g hg => by
    simp only [List.mem_append, or_self] at hg
    exact hw g hg) h
  simp only [xw_append] at h1
  rw [← h1]
  simp only [pow_succ, pow_zero, one_mul]

theorem comm_of_word {u v : List ℕ} (hu : ∀ g ∈ u, g < 12) (hv : ∀ g ∈ v, g < 12)
    (h : Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (u ++ v) CFSG.KD.BrFi24.ONE)
      (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (v ++ u) CFSG.KD.BrFi24.ONE) = true) :
    xw u * xw v = xw v * xw u := by
  have hl : ∀ {x y : List ℕ}, (∀ g ∈ x, g < 12) → (∀ g ∈ y, g < 12) → ∀ g ∈ x ++ y, g < 12 := by
    intro x y hx hy g hg
    rcases List.mem_append.1 hg with h | h
    · exact hx g h
    · exact hy g h
  have := xw_eq_beq (hl hu hv) (hl hv hu) h
  rwa [xw_append, xw_append] at this

theorem pair0 : ∃ a ∈ seedGrp, ∃ b ∈ seedGrp, a * sE 0 = sE 0 * a ∧ b * sE 0 = sE 0 * b ∧
    orderOf a = 7 ∧ orderOf b = 7 ∧
    81 ∣ Nat.card (Subgroup.closure ({a, b} : Set (GL (Fin 781) (ZMod 3)))) := by
  have h3159 : 3159 ∣ Nat.card (Subgroup.closure ({xw J.A0, xw J.B0} : Set (GL (Fin 781) (ZMod 3)))) :=
    dvd_of_pt A0_lt B0_lt (m := 3159) (F := F0) (PA := PA0) (PB := PB0) (PAR := PAR0)
      (DEP := DEP0) (by norm_num) (fun j hj => incStep_spec (and4 (ok0_spec j hj)).1)
      (fun j hj => wStep_spec (and4 (ok0_spec j hj)).2.1)
      (fun j hj => wStep_spec (and4 (ok0_spec j hj)).2.2.1)
      (fun j hj => tStep_spec (and4 (ok0_spec j hj)).2.2.2)
  have h81 := Nat.dvd_trans (by norm_num : 81 ∣ 3159) h3159
  obtain ⟨oa, ob⟩ := order7 (pow7_of_word A0_lt MS.a0) (pow7_of_word B0_lt MS.b0) h81
  exact ⟨xw J.A0, xw_mem A0_lt (even _ (by simp)), xw J.B0, xw_mem B0_lt (even _ (by simp)),
    comm_of_word A0_lt S0_lt MS.a0s, comm_of_word B0_lt S0_lt MS.b0s, oa, ob, h81⟩

theorem t2_sq : xw J.T2 * xw J.T2 = 1 := by
  rw [T2_eq, ← xw_append]
  simp [xw, wq, g0_mul_self]

theorem pair2 : ∃ a ∈ seedGrp, ∃ b ∈ seedGrp, a * sE 2 = sE 2 * a ∧ b * sE 2 = sE 2 * b ∧
    orderOf a = 7 ∧ orderOf b = 7 ∧
    81 ∣ Nat.card (Subgroup.closure ({a, b} : Set (GL (Fin 781) (ZMod 3)))) := by
  have h5670 : 5670 ∣ Nat.card (Subgroup.closure ({xw J.A2, xw B2} : Set (GL (Fin 781) (ZMod 3)))) :=
    dvd_of_pairs A2_lt B2_lt (m1 := 378) (M := 5670) (F := F2) (PA := PA2) (PB := PB2)
      (Q := Q2) (QA := QA2) (QB := QB2) (QP := QP2) (QD := QD2) (by norm_num)
      (fun j hj => incStep_spec (and3 (pt2_spec j hj)).1)
      (fun j hj => wStep_spec (and3 (pt2_spec j hj)).2.1)
      (fun j hj => wStep_spec (and3 (pt2_spec j hj)).2.2)
      (fun k hk => qIncStep_spec (and4 (pr2_spec k hk)).1)
      (fun k hk => qStep_spec (and4 (pr2_spec k hk)).2.1)
      (fun k hk => qStep_spec (and4 (pr2_spec k hk)).2.2.1)
      (fun k hk => tStep_spec (and4 (pr2_spec k hk)).2.2.2)
  have h81 := Nat.dvd_trans (by norm_num : 81 ∣ 5670) h5670
  obtain ⟨cA, vA⟩ := mat_A2
  have a7 : xw J.A2 ^ 7 = 1 := pow7_of_mat cA vA MS.a2
  have hb : xw B2 = xw J.T2 * xw J.A2 * xw J.T2 := by rw [B2, xw_append, xw_append]
  have b7 : xw B2 ^ 7 = 1 := by
    rw [hb]
    have e : ∀ n : ℕ, (xw J.T2 * xw J.A2 * xw J.T2) ^ n = xw J.T2 * xw J.A2 ^ n * xw J.T2 := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, mul_one, t2_sq]
      | succ n ih =>
        rw [pow_succ, ih, pow_succ]
        calc xw J.T2 * xw J.A2 ^ n * xw J.T2 * (xw J.T2 * xw J.A2 * xw J.T2) =
            xw J.T2 * xw J.A2 ^ n * (xw J.T2 * xw J.T2) * xw J.A2 * xw J.T2 := by group
          _ = xw J.T2 * (xw J.A2 ^ n * xw J.A2) * xw J.T2 := by rw [t2_sq]; group
    rw [e, a7, mul_one, t2_sq]
  obtain ⟨oa, ob⟩ := order7 a7 b7 h81
  have hts : xw J.T2 * xw J.S2 = xw J.S2 * xw J.T2 := comm_of_word T2_lt S2_lt MS.t2s
  have has : xw J.A2 * xw J.S2 = xw J.S2 * xw J.A2 := by
    obtain ⟨cS, vS⟩ := wordMul_τ cn_one J.S2 S2_lt
    obtain ⟨-, vSA⟩ := wordMul_τ cA J.S2 S2_lt
    obtain ⟨-, vAS⟩ := mul_mt cA cS
    have e := congrArg Mt (eq_of_beq' MS.a2s)
    rw [vSA, vAS, vS, mt_one, Matrix.mul_one, ← vA] at e
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    exact e.symm
  refine ⟨xw J.A2, xw_mem A2_lt (even _ (by simp)), xw B2, xw_mem B2_lt (even _ (by simp)), has, ?_,
    oa, ob, h81⟩
  change xw B2 * xw J.S2 = xw J.S2 * xw B2
  rw [hb]
  calc xw J.T2 * xw J.A2 * xw J.T2 * xw J.S2 = xw J.T2 * xw J.A2 * (xw J.T2 * xw J.S2) := by group
    _ = xw J.T2 * (xw J.A2 * xw J.S2) * xw J.T2 := by rw [hts]; group
    _ = (xw J.T2 * xw J.S2) * xw J.A2 * xw J.T2 := by rw [has]; group
    _ = xw J.S2 * (xw J.T2 * xw J.A2 * xw J.T2) := by rw [hts]; group

theorem pair4 : ∃ a ∈ seedGrp, ∃ b ∈ seedGrp, a * sE 4 = sE 4 * a ∧ b * sE 4 = sE 4 * b ∧
    orderOf a = 7 ∧ orderOf b = 7 ∧
    81 ∣ Nat.card (Subgroup.closure ({a, b} : Set (GL (Fin 781) (ZMod 3)))) := by
  have h44226 : 44226 ∣ Nat.card (Subgroup.closure ({xw J.A4, xw J.B4} :
      Set (GL (Fin 781) (ZMod 3)))) :=
    dvd_of_pairs A4_lt B4_lt (m1 := 351) (M := 44226) (F := F4) (PA := PA4) (PB := PB4)
      (Q := Q4) (QA := QA4) (QB := QB4) (QP := QP4) (QD := QD4) (by norm_num)
      (fun j hj => incStep_spec (and3 (pt4_spec j hj)).1)
      (fun j hj => wStep_spec (and3 (pt4_spec j hj)).2.1)
      (fun j hj => wStep_spec (and3 (pt4_spec j hj)).2.2)
      (fun k hk => qIncStep_spec (and4 (pr4_spec k hk)).1)
      (fun k hk => qStep_spec (and4 (pr4_spec k hk)).2.1)
      (fun k hk => qStep_spec (and4 (pr4_spec k hk)).2.2.1)
      (fun k hk => tStep_spec (and4 (pr4_spec k hk)).2.2.2)
  have h81 := Nat.dvd_trans (by norm_num : 81 ∣ 44226) h44226
  obtain ⟨cA, vA⟩ := mat_A4
  obtain ⟨cB, vB⟩ := mat_B4
  obtain ⟨cZ, vZ⟩ := mat_S4
  obtain ⟨oa, ob⟩ := order7 (pow7_of_mat cA vA MS.a4) (pow7_of_mat cB vB MS.b4) h81
  have comm : ∀ {X : ℕ} (hX : Cn X) {x : GL (Fin 781) (ZMod 3)},
      (x : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt X →
      Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.Fi24P7.MX 32) X)
        (CFSG.KD.BrFi24.MUL X (CFSG.KD.Fi24P7.MX 32)) = true →
      x * xw J.S4 = xw J.S4 * x := by
    intro X hX x hx h
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hx, vZ, ← (mul_mt hX cZ).2, ← (mul_mt cZ hX).2,
      eq_of_beq' h]
  exact ⟨xw J.A4, xw_mem A4_lt (even _ (by simp)), xw J.B4, xw_mem B4_lt (even _ (by simp)),
    comm cA vA MS.a4s, comm cB vB MS.b4s, oa, ob, h81⟩

theorem fi24_three_pairs : ∃ s : Fin 5 → GL (Fin 781) (ZMod 3),
    (∀ i, s i ∈ seedGrp ∧ s i ^ 3 = 1 ∧ s i ≠ 1) ∧
    Nat.card (ptFix (s 0)) = 3240 ∧ Nat.card (ptFix (s 1)) = 1485 ∧
    Nat.card (ptFix (s 2)) = 378 ∧ Nat.card (ptFix (s 3)) = 162 ∧ Nat.card (ptFix (s 4)) = 0 ∧
    ∀ i : Fin 5, i = 0 ∨ i = 2 ∨ i = 4 → ∃ a ∈ seedGrp, ∃ b ∈ seedGrp,
      a * s i = s i * a ∧ b * s i = s i * b ∧ orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card (Subgroup.closure ({a, b} : Set (GL (Fin 781) (ZMod 3)))) := by
  refine ⟨sE, s_facts, card0, card1, card2, card3, card4, ?_⟩
  rintro i (rfl | rfl | rfl)
  · exact pair0
  · exact pair2
  · exact pair4

end CertificateChecks.KernelFi24P7

end
