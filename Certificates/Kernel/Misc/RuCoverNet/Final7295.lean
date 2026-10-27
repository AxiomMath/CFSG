module

public import Certificates.Kernel.Misc.RuCoverNet.Checks7295
public import CFSG.Certificates.Kernel.Misc.RuCoverNetSound
public import Certificates.Kernel.Misc.RuCover.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.SzCoverNative
import Mathlib.Tactic.IntervalCases
import all CFSG.Sporadic.Recognition.RuMultiplierInputs
import all CFSG.Sporadic.Presentation.RuExactInputs
import all CFSG.LieType.Multipliers.CoverWords
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuCoverNet

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.RuCover
  CFSG.EvenSporadicStandard.Induction.RuSz CFSG.EvenSporadicStandard.TwoRu.SzCover

local notation "Ψ" j:max => CFSG.KC.YModel.Sch.netPerm 14 16240 (CFSG.KD.RuCoverNet.U j)

theorem cperm_ev {k n : Nat} {U : Nat → Nat} (j : Nat) :
    CFSG.KC.YModel.Sch.cperm k n U (2 * j + 2) = CFSG.KC.YModel.Sch.netPerm k n (U j) := by
  have h1 : (2 * j + 2).testBit 0 = false := by
    rw [Nat.testBit_zero]
    exact decide_eq_false (by omega)
  have h2 : (2 * j + 2) >>> 1 - 1 = j := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  unfold CFSG.KC.YModel.Sch.cperm
  rw [h1, h2]
  simp

theorem cperm_od {k n : Nat} {U : Nat → Nat} (j : Nat) :
    CFSG.KC.YModel.Sch.cperm k n U (2 * j + 3) = (CFSG.KC.YModel.Sch.netPerm k n (U j))⁻¹ := by
  have h1 : (2 * j + 3).testBit 0 = true := by
    rw [Nat.testBit_zero]
    exact decide_eq_true (by omega)
  have h2 : (2 * j + 3) >>> 1 - 1 = j := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  unfold CFSG.KC.YModel.Sch.cperm
  rw [h1, h2]
  simp

theorem cpermL_cons {k n : Nat} {U : Nat → Nat} (x : Nat) (cs : List Nat) :
    CFSG.KC.YModel.Sch.cpermL k n U (x :: cs) =
      CFSG.KC.YModel.Sch.cperm k n U x * CFSG.KC.YModel.Sch.cpermL k n U cs := by
  unfold CFSG.KC.YModel.Sch.cpermL
  rw [List.map_cons, List.prod_cons]

theorem cpermL_nil {k n : Nat} {U : Nat → Nat} : CFSG.KC.YModel.Sch.cpermL k n U [] = 1 := rfl

theorem hlet : ∀ g < 3, CFSG.KC.YModel.letOK 14 16240
    (CFSG.KC.Misc.RuCoverNet.F CFSG.KAct.RuRho.A (Nat.add (Nat.mul 2 g) 1))
    (CFSG.KD.RuCoverNet.U g) = true := by
  intro g hg
  interval_cases g
  exacts [CFSG.KD.RuCoverNet.ch7295l0, CFSG.KD.RuCoverNet.ch7295l1, CFSG.KD.RuCoverNet.ch7295l2]

theorem hwords : ∀ i < 17, CFSG.KC.YModel.wordOK 14 6 3 CFSG.KD.RuCoverNet.U
    CFSG.KD.RuCoverNet.GP CFSG.KD.RuCoverNet.GL i = true := by
  intro i hi
  interval_cases i
  exacts [CFSG.KD.RuCoverNet.ch7295w0, CFSG.KD.RuCoverNet.ch7295w1, CFSG.KD.RuCoverNet.ch7295w2,
    CFSG.KD.RuCoverNet.ch7295w3, CFSG.KD.RuCoverNet.ch7295w4, CFSG.KD.RuCoverNet.ch7295w5,
    CFSG.KD.RuCoverNet.ch7295w6, CFSG.KD.RuCoverNet.ch7295w7, CFSG.KD.RuCoverNet.ch7295w8,
    CFSG.KD.RuCoverNet.ch7295w9, CFSG.KD.RuCoverNet.ch7295w10, CFSG.KD.RuCoverNet.ch7295w11,
    CFSG.KD.RuCoverNet.ch7295w12, CFSG.KD.RuCoverNet.ch7295w13, CFSG.KD.RuCoverNet.ch7295w14,
    CFSG.KD.RuCoverNet.ch7295w15, CFSG.KD.RuCoverNet.ch7295w16]

theorem hrels : ∀ i < 6, CFSG.KC.YModel.sweqK 14 6 CFSG.KD.RuCoverNet.U (CFSG.KD.RuCoverNet.RP i)
    (CFSG.KD.RuCoverNet.RL i) 0 0 = true := by
  intro i hi
  interval_cases i
  exacts [CFSG.KD.RuCoverNet.ch7295r0, CFSG.KD.RuCoverNet.ch7295r1, CFSG.KD.RuCoverNet.ch7295r2,
    CFSG.KD.RuCoverNet.ch7295r3, CFSG.KD.RuCoverNet.ch7295r4, CFSG.KD.RuCoverNet.ch7295r5]

theorem psi_letter (hRho : ruRhoCheck = true) : ∀ g < 3,
    CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet.U g) ∧ Ψ g = ruRhoGen g := by
  obtain ⟨σ, hσ, hgen⟩ := CertificateChecks.KernelMisc.RuCover.rep_A hRho
  intro g hg
  obtain ⟨h1, h2⟩ := CFSG.KC.Misc.RuCoverNet.letter_perm hσ hlet ⟨g, hg⟩
  exact ⟨h1, h2.trans (hgen ⟨g, hg⟩).symm⟩

theorem psi_chain (hRho : ruRhoCheck = true) : ∀ j < 20,
    CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet.U j) ∧
      ∀ i, j = 3 + i → Ψ j = CFSG.KC.YModel.Sch.cpermL 14 16240 CFSG.KD.RuCoverNet.U
        (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP i) (CFSG.KD.RuCoverNet.GL i)) :=
  CFSG.KC.Misc.RuCoverNet.chain_spec (E := 17) (by norm_num) (by norm_num)
    (fun c hc => (psi_letter hRho c hc).1) hwords

theorem psi_good (hRho : ruRhoCheck = true) {j : Nat} (hj : j < 20) :
    CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet.U j) := (psi_chain hRho j hj).1

theorem psi_val (hRho : ruRhoCheck = true) {i : Nat} (hi : i < 17) {cs : List Nat}
    (hc : CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP i) (CFSG.KD.RuCoverNet.GL i) = cs) :
    Ψ (3 + i) = CFSG.KC.YModel.Sch.cpermL 14 16240 CFSG.KD.RuCoverNet.U cs := by
  rw [← hc]
  exact (psi_chain hRho (3 + i) (by omega)).2 i rfl

theorem codes_a : (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 0)
    (CFSG.KD.RuCoverNet.GL 0)).map CFSG.KC.YModel.TextSem.decI = zword ruP0 := by
  rw [CertificateChecks.KernelCosetJ.RhoRu.ruP0_eq]
  decide +kernel

theorem codes_b : (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 1)
    (CFSG.KD.RuCoverNet.GL 1)).map CFSG.KC.YModel.TextSem.decI = zword ruP1 := by
  rw [CertificateChecks.KernelMisc.RuCover.ruP1_eq]
  decide +kernel

theorem codes_rows :
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 2) (CFSG.KD.RuCoverNet.GL 2) = [8, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 3) (CFSG.KD.RuCoverNet.GL 3) = [12, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 4) (CFSG.KD.RuCoverNet.GL 4) = [12, 14] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 5) (CFSG.KD.RuCoverNet.GL 5) = [12, 16] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 6) (CFSG.KD.RuCoverNet.GL 6) = [18, 16] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 7) (CFSG.KD.RuCoverNet.GL 7) =
      [20, 20, 20, 20, 20] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 8) (CFSG.KD.RuCoverNet.GL 8) =
      [16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 9) (CFSG.KD.RuCoverNet.GL 9) = [12, 24] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 10) (CFSG.KD.RuCoverNet.GL 10) = [27] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 11) (CFSG.KD.RuCoverNet.GL 11) = [28, 22] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 12) (CFSG.KD.RuCoverNet.GL 12) = [30, 26] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 13) (CFSG.KD.RuCoverNet.GL 13) =
      [32, 32, 8, 32] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 14) (CFSG.KD.RuCoverNet.GL 14) =
      [32, 8, 32, 32] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 15) (CFSG.KD.RuCoverNet.GL 15) =
      [36, 34, 8, 36, 34, 8] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 16) (CFSG.KD.RuCoverNet.GL 16) =
      [34, 8, 34, 36, 34, 8, 34, 8, 34, 8, 8] := by
  decide +kernel

theorem codes_z :
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.ZP 0) (CFSG.KD.RuCoverNet.ZL 0) = [8, 8, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.ZP 1) (CFSG.KD.RuCoverNet.ZL 1) =
      [10, 8, 8] := by
  decide +kernel

@[expose] def encR (l : ℕ × Bool) : ℕ :=
  if l.1 = 0 then (if l.2 then 38 else 39) else (if l.2 then 40 else 41)

theorem codes_rel : ∀ i < 6, CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.RP i)
    (CFSG.KD.RuCoverNet.RL i) = (szRels.getD i []).map encR := by
  decide +kernel

theorem rels_eq : szRels = (List.range 6).map fun i => szRels.getD i [] := by
  decide +kernel

@[expose] def pval {G : Type*} [Group G] (s t : G) (v : List (ℕ × Bool)) : G :=
  (v.map fun l => if l.1 = 0 then (if l.2 then s else s⁻¹) else (if l.2 then t else t⁻¹)).prod

theorem pval_cons {G : Type*} [Group G] (s t : G) (l : ℕ × Bool) (v : List (ℕ × Bool)) :
    pval s t (l :: v) =
      (if l.1 = 0 then (if l.2 then s else s⁻¹) else (if l.2 then t else t⁻¹)) * pval s t v := by
  unfold pval
  rw [List.map_cons, List.prod_cons]

theorem rep_szPwordA {n : ℕ} {S Sinv T Tinv : Array ℕ} {s t : Equiv.Perm (Fin n)}
    (hS : Rep n S s) (hSi : Rep n Sinv s⁻¹) (hT : Rep n T t) (hTi : Rep n Tinv t⁻¹) :
    ∀ v, Rep n (szPwordA n S Sinv T Tinv v) (pval s t v)
  | [] => rep_idA
  | l :: v => by
    rw [szPwordA, pval_cons]
    refine rep_compA ?_ (rep_szPwordA hS hSi hT hTi v)
    split_ifs
    · exact hS
    · exact hSi
    · exact hT
    · exact hTi

theorem map_pval {G H : Type*} [Group G] [Group H] (f : G →* H) (s t : G) (v : List (ℕ × Bool)) :
    f (pval s t v) = pval (f s) (f t) v := by
  unfold pval
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  split_ifs <;> simp

theorem cpermL_encR {k n : Nat} {U : Nat → Nat} : ∀ v : List (ℕ × Bool),
    CFSG.KC.YModel.Sch.cpermL k n U (v.map encR) =
      pval (CFSG.KC.YModel.Sch.netPerm k n (U 18)) (CFSG.KC.YModel.Sch.netPerm k n (U 19)) v
  | [] => rfl
  | l :: v => by
    rw [List.map_cons, cpermL_cons, cpermL_encR v, pval_cons]
    congr 1
    unfold encR
    split_ifs
    · exact cperm_ev 18
    · exact cperm_od 18
    · exact cperm_ev 19
    · exact cperm_od 19

theorem slotRunA_flag {n : ℕ} (rows : List SlotRow) {t₁ t₂ : Array ℕ}
    {g₁ g₂ : Equiv.Perm (Fin n)} (h₁ : Rep n t₁ g₁) (h₂ : Rep n t₂ g₂) :
    (slotRunA n rows t₁ t₂).2.2 = true := by
  have key : ∀ (rows : List SlotRow) (a : List (ℕ × Array ℕ) × Bool)
      (s : List (ℕ × Equiv.Perm (Fin n))), SlotRep n a.1 s → a.2 = true →
      (rows.foldl (slotStepA n) a).2 = true := by
    intro rows
    induction rows with
    | nil => intro a s _ hf; exact hf
    | cons r rows ih =>
      intro a s h hf
      rw [List.foldl_cons]
      cases r with
      | mu i j k =>
        exact ih _ ((k, slotRead s i * slotRead s j) :: s)
          (List.Forall₂.cons ⟨rfl, rep_compA (slotRep_read h i) (slotRep_read h j)⟩ h) hf
      | iv i j =>
        have hi := CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep (slotRep_read h i)
        refine ih _ ((j, (slotRead s i)⁻¹) :: s)
          (List.Forall₂.cons ⟨rfl, rep_inv_of_isInvA (slotRep_read h i) hi⟩ h) ?_
        simp only [slotStepA, Bool.and_eq_true]
        exact ⟨hf, hi⟩
      | pwr e i j =>
        exact ih _ ((j, slotRead s i ^ e) :: s)
          (List.Forall₂.cons ⟨rfl, rep_powA (slotRep_read h i) e⟩ h) hf
  exact key rows _ [(1, g₁), (2, g₂)]
    (List.Forall₂.cons ⟨rfl, h₁⟩ (List.Forall₂.cons ⟨rfl, h₂⟩ List.Forall₂.nil)) rfl

theorem rep_inv' {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ :=
  rep_inv_of_isInvA ht (CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep ht)

theorem rep_wordA2 {n : ℕ} {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u h) (w : List ℤ) (hw : lettersOK 2 w = true) :
    Rep n (wordA n #[t, u] #[invCand n t, invCand n u] w) (evalSigned [g, h] w) := by
  refine rep_wordA_evalSigned (k := 2) (fun i hi => ?_) (fun i hi => ?_) w hw
  · interval_cases i
    · exact ht
    · exact hu
  · interval_cases i
    · exact rep_inv' ht
    · exact rep_inv' hu

theorem rep_wordA3 {n : ℕ} {t u v : Array ℕ} {g h f : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u h) (hv : Rep n v f) (w : List ℤ) (hw : lettersOK 3 w = true) :
    Rep n (wordA n #[t, u, v] (#[t, u, v].map (invCand n)) w) (evalSigned [g, h, f] w) := by
  refine rep_wordA_evalSigned (k := 3) (fun i hi => ?_) (fun i hi => ?_) w hw
  · interval_cases i
    · exact ht
    · exact hu
    · exact hv
  · rw [getElem!_map_of_lt (A := #[t, u, v]) (by simpa using hi)]
    interval_cases i
    · exact rep_inv' ht
    · exact rep_inv' hu
    · exact rep_inv' hv

section Main


theorem hRho : ruRhoCheck = true := Certificates.certificate15025

theorem hS : ∀ j < 3, Rep 16240 ruRhoArrs[j]! (Ψ j) ∧
    (ruRhoArrs.map (invCand 16240))[j]! = invCand 16240 ruRhoArrs[j]! := by
  intro j hj
  have hs : ruRhoArrs.size = 3 := rfl
  refine ⟨?_, getElem!_map_of_lt (by omega)⟩
  rw [(psi_letter hRho j hj).2]
  exact rep_of_allPermsOK (rho_facts hRho).1 (by omega)

theorem rep_elem {i : Nat} (hi : i < 17) {w : List ℤ}
    (hc : (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP i) (CFSG.KD.RuCoverNet.GL i)).map
      CFSG.KC.YModel.TextSem.decI = w)
    (hb : (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP i) (CFSG.KD.RuCoverNet.GL i)).all
      (fun x => decide (1 < x) && decide (x >>> 1 ≤ 3)) = true) :
    Rep 16240 (wordArr 16240 ruRhoArrs w) (Ψ (3 + i)) := by
  have hcodes : ∀ x ∈ CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP i)
      (CFSG.KD.RuCoverNet.GL i), 1 < x ∧ x >>> 1 ≤ 3 := fun x hx => by
    have h := List.all_eq_true.1 hb x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  have h := CFSG.KC.YModel.Chain.rep_wordA (J := 3) hS _ hcodes
  rw [hc] at h
  rw [psi_val hRho hi rfl]
  exact h

theorem codes_ab : (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 0)
      (CFSG.KD.RuCoverNet.GL 0)).all (fun x => decide (1 < x) && decide (x >>> 1 ≤ 3)) = true ∧
    (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 1)
      (CFSG.KD.RuCoverNet.GL 1)).all (fun x => decide (1 < x) && decide (x >>> 1 ≤ 3)) = true := by
  decide +kernel

theorem rep_p0 : Rep 16240 (p0A ()) (Ψ 3) :=
  rep_elem (i := 0) (by norm_num) codes_a codes_ab.1

theorem rep_p1 : Rep 16240 (p1A ()) (Ψ 4) :=
  rep_elem (i := 1) (by norm_num) codes_b codes_ab.2

theorem e5 : Ψ 5 = Ψ 3 * Ψ 4 := by
  have h := psi_val hRho (i := 2) (by norm_num) codes_rows.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 3, cperm_ev 4] at h
  exact h

theorem e6 : Ψ 6 = Ψ 5 * Ψ 4 := by
  have h := psi_val hRho (i := 3) (by norm_num) codes_rows.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 5, cperm_ev 4] at h
  exact h

theorem e7 : Ψ 7 = Ψ 5 * Ψ 6 := by
  have h := psi_val hRho (i := 4) (by norm_num) codes_rows.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 5, cperm_ev 6] at h
  exact h

theorem e8 : Ψ 8 = Ψ 5 * Ψ 7 := by
  have h := psi_val hRho (i := 5) (by norm_num) codes_rows.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 5, cperm_ev 7] at h
  exact h

theorem e9 : Ψ 9 = Ψ 8 * Ψ 7 := by
  have h := psi_val hRho (i := 6) (by norm_num) codes_rows.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 8, cperm_ev 7] at h
  exact h

theorem e10 : Ψ 10 = Ψ 9 ^ 5 := by
  have h := psi_val hRho (i := 7) (by norm_num) codes_rows.2.2.2.2.2.1
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 9] at h
  rw [h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem e11 : Ψ 11 = Ψ 7 ^ 11 := by
  have h := psi_val hRho (i := 8) (by norm_num) codes_rows.2.2.2.2.2.2.1
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 7] at h
  rw [h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem e12 : Ψ 12 = Ψ 5 * Ψ 11 := by
  have h := psi_val hRho (i := 9) (by norm_num) codes_rows.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 5, cperm_ev 11] at h
  exact h

theorem e13 : Ψ 13 = (Ψ 12)⁻¹ := by
  have h := psi_val hRho (i := 10) (by norm_num) codes_rows.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_nil, mul_one, cperm_od 12] at h
  exact h

theorem e14 : Ψ 14 = Ψ 13 * Ψ 10 := by
  have h := psi_val hRho (i := 11) (by norm_num) codes_rows.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 13, cperm_ev 10] at h
  exact h

theorem e15 : Ψ 15 = Ψ 14 * Ψ 12 := by
  have h := psi_val hRho (i := 12) (by norm_num) codes_rows.2.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 14, cperm_ev 12] at h
  exact h

theorem e16 : Ψ 16 = Ψ 15 * (Ψ 15 * (Ψ 3 * Ψ 15)) := by
  have h := psi_val hRho (i := 13) (by norm_num) codes_rows.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 15, cperm_ev 3] at h
  exact h

theorem e17 : Ψ 17 = Ψ 15 * (Ψ 3 * (Ψ 15 * Ψ 15)) := by
  have h := psi_val hRho (i := 14) (by norm_num) codes_rows.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 15, cperm_ev 3] at h
  exact h

theorem e18 : Ψ 18 = Ψ 17 * (Ψ 16 * (Ψ 3 * (Ψ 17 * (Ψ 16 * Ψ 3)))) := by
  have h := psi_val hRho (i := 15) (by norm_num) codes_rows.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 17, cperm_ev 16, cperm_ev 3] at h
  exact h

theorem e19 : Ψ 19 = Ψ 16 * (Ψ 3 * (Ψ 16 * (Ψ 17 * (Ψ 16 * (Ψ 3 * (Ψ 16 * (Ψ 3 * (Ψ 16 *
    (Ψ 3 * Ψ 3))))))))) := by
  have h := psi_val hRho (i := 16) (by norm_num) codes_rows.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 17, cperm_ev 16, cperm_ev 3] at h
  exact h

theorem ez : Ψ 3 * Ψ 3 * Ψ 4 = Ψ 4 * (Ψ 3 * Ψ 3) := by
  have g : ∀ x ∈ ([8, 8, 10] : List Nat), CFSG.KC.YModel.Sch.Good 14 16240
      (CFSG.KD.RuCoverNet.U ((x >>> 1) - 1)) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact psi_good hRho (by decide)
    · exact psi_good hRho (by decide)
    · exact psi_good hRho (by decide)
  have g' : ∀ x ∈ ([10, 8, 8] : List Nat), CFSG.KC.YModel.Sch.Good 14 16240
      (CFSG.KD.RuCoverNet.U ((x >>> 1) - 1)) := fun x hx => g x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        omega)
  have h := CFSG.KC.YModel.Sch.sweqK_spec (n := 16240) (by norm_num)
    (codes_z.1 ▸ g) (codes_z.2 ▸ g') CFSG.KD.RuCoverNet.ch7295z0
  rw [codes_z.1, codes_z.2] at h
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 3, cperm_ev 4] at h
  rw [mul_assoc, h]

theorem slotRun_eq : slotRun ruMProg (Ψ 3) (Ψ 4) = (Ψ 3, Ψ 15) := by
  rw [e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5]
  rfl

theorem mw0 : evalSigned [Ψ 3, Ψ 15] (ruLMWords.getD 0 []) = Ψ 3 := by
  simp [evalSigned, ruLMWords]

theorem mw1 : evalSigned [Ψ 3, Ψ 15] (ruLMWords.getD 1 []) = Ψ 16 := by
  rw [e16]
  simp [evalSigned, ruLMWords]

theorem mw2 : evalSigned [Ψ 3, Ψ 15] (ruLMWords.getD 2 []) = Ψ 17 := by
  rw [e17]
  simp [evalSigned, ruLMWords]

theorem sM_eq : evalSigned [Ψ 3, Ψ 16, Ψ 17] sWord = Ψ 18 := by
  rw [e18]
  simp [evalSigned, sWord]

theorem tM_eq : evalSigned [Ψ 3, Ψ 16, Ψ 17] tWord * (Ψ 3 * Ψ 3) = Ψ 19 := by
  rw [e19]
  simp [evalSigned, tWord, mul_assoc]

theorem rel_net : ∀ v ∈ szRels, pval (Ψ 18) (Ψ 19) v = 1 := by
  intro v hv
  rw [rels_eq, List.mem_map] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have hi6 : i < 6 := List.mem_range.1 hi
  have e := codes_rel i hi6
  have hg : CFSG.KC.YModel.Sch.CodesGood 14 16240 CFSG.KD.RuCoverNet.U
      (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.RP i) (CFSG.KD.RuCoverNet.RL i)) := by
    rw [e]
    intro x hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    unfold encR
    split_ifs
    all_goals exact psi_good hRho (by decide)
  have hg0 : CFSG.KC.YModel.Sch.CodesGood 14 16240 CFSG.KD.RuCoverNet.U
      (CFSG.KC.YModel.Sch.codesL 6 0 0) := fun x hx => by
    simp [CFSG.KC.YModel.Sch.codesL] at hx
  have h := CFSG.KC.YModel.Sch.sweqK_spec (n := 16240) (by norm_num) hg hg0 (hrels i hi6)
  rw [e, cpermL_encR] at h
  exact h.trans rfl

theorem closure_le_cent : Subgroup.closure ({Ψ 3, Ψ 4} : Set (Equiv.Perm (Fin 16240))) ≤
    Subgroup.centralizer {Ψ 3 * Ψ 3} := by
  rw [Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rcases hx with rfl | hx
  · rw [mul_assoc]
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ez

theorem szCoverChk_true : szCoverChk () = true := by
  have r0 := rep_p0
  have r1 := rep_p1
  have hflag := slotRunA_flag (n := 16240) ruMProg r0 r1
  have hm := rep_slotRunA ruMProg r0 r1 hflag
  rw [slotRun_eq] at hm
  obtain ⟨rM1, rM2⟩ := hm
  have rMW : ∀ w, lettersOK 2 w = true →
      Rep 16240 (szMWordA 16240 (p0A ()) (p1A ()) w) (evalSigned [Ψ 3, Ψ 15] w) :=
    fun w hw => rep_wordA2 rM1 rM2 w hw
  set Wg := evalSigned [Ψ 3, Ψ 4] ruAlignmentSeedWord with hWg
  set Rg := evalSigned [Ψ 3, Ψ 15] ruRMWord with hRg
  set Hg := (Wg * Rg * Wg⁻¹ * Ψ 3) ^ 7 * Wg with hHg
  have rW : Rep 16240 (szWA 16240 (p0A ()) (p1A ())) Wg := rep_wordA2 r0 r1 _ (by decide)
  have rU : Rep 16240 (szUA 16240 (p0A ()) (p1A ())) (Wg * Rg * Wg⁻¹ * Ψ 3) :=
    rep_compA (rep_compA (rep_compA rW (rMW _ (by decide))) (rep_inv' rW)) r0
  have rH : Rep 16240 (szHA 16240 (p0A ()) (p1A ())) Hg := rep_compA (rep_powA rU 7) rW
  have rL : ∀ i < 3, Rep 16240 (szLA 16240 (p0A ()) (p1A ()) i)
      (Hg * evalSigned [Ψ 3, Ψ 15] (ruLMWords.getD i []) * Hg⁻¹) := by
    intro i hi
    have hw : lettersOK 2 (ruLMWords.getD i []) = true := by
      interval_cases i <;> decide
    exact rep_compA (rep_compA rH (rMW _ hw)) (rep_inv' rH)
  set f : Equiv.Perm (Fin 16240) →* Equiv.Perm (Fin 16240) := (MulAut.conj Hg).toMonoidHom
    with hf
  have hfx : ∀ x, f x = Hg * x * Hg⁻¹ := fun x => rfl
  have rL0 : Rep 16240 (szLA 16240 (p0A ()) (p1A ()) 0) (f (Ψ 3)) := by
    rw [hfx, ← mw0]
    exact rL 0 (by norm_num)
  have rL1 : Rep 16240 (szLA 16240 (p0A ()) (p1A ()) 1) (f (Ψ 16)) := by
    rw [hfx, ← mw1]
    exact rL 1 (by norm_num)
  have rL2 : Rep 16240 (szLA 16240 (p0A ()) (p1A ()) 2) (f (Ψ 17)) := by
    rw [hfx, ← mw2]
    exact rL 2 (by norm_num)
  have rSA : Rep 16240 (szSA 16240 (p0A ()) (p1A ()))
      (evalSigned [f (Ψ 3), f (Ψ 16), f (Ψ 17)] sWord) :=
    rep_wordA3 rL0 rL1 rL2 sWord (by decide)
  have rTA : Rep 16240 (szTA 16240 (p0A ()) (p1A ()))
      (evalSigned [f (Ψ 3), f (Ψ 16), f (Ψ 17)] tWord * (Ψ 3 * Ψ 3)) :=
    rep_compA (rep_wordA3 rL0 rL1 rL2 tWord (by decide)) (rep_compA r0 r0)
  let K := Subgroup.closure ({Ψ 3, Ψ 4} : Set (Equiv.Perm (Fin 16240)))
  have h3 : Ψ 3 ∈ K := Subgroup.subset_closure (by simp)
  have h4 : Ψ 4 ∈ K := Subgroup.subset_closure (by simp)
  have m5 : Ψ 5 ∈ K := by rw [e5]; exact K.mul_mem h3 h4
  have m6 : Ψ 6 ∈ K := by rw [e6]; exact K.mul_mem m5 h4
  have m7 : Ψ 7 ∈ K := by rw [e7]; exact K.mul_mem m5 m6
  have m8 : Ψ 8 ∈ K := by rw [e8]; exact K.mul_mem m5 m7
  have m9 : Ψ 9 ∈ K := by rw [e9]; exact K.mul_mem m8 m7
  have m10 : Ψ 10 ∈ K := by rw [e10]; exact K.pow_mem m9 5
  have m11 : Ψ 11 ∈ K := by rw [e11]; exact K.pow_mem m7 11
  have m12 : Ψ 12 ∈ K := by rw [e12]; exact K.mul_mem m5 m11
  have m13 : Ψ 13 ∈ K := by rw [e13]; exact K.inv_mem m12
  have m14 : Ψ 14 ∈ K := by rw [e14]; exact K.mul_mem m13 m10
  have m15 : Ψ 15 ∈ K := by rw [e15]; exact K.mul_mem m14 m12
  have hWm : Wg ∈ K := evalSigned_mem (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [h3, h4]) _
  have hRm : Rg ∈ K := evalSigned_mem (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [h3, m15]) _
  have hHm : Hg ∈ K :=
    K.mul_mem (K.pow_mem (K.mul_mem (K.mul_mem (K.mul_mem hWm hRm) (K.inv_mem hWm)) h3) 7) hWm
  have hzH : Ψ 3 * Ψ 3 * Hg = Hg * (Ψ 3 * Ψ 3) :=
    Subgroup.mem_centralizer_iff.1 (closure_le_cent hHm) _ (Set.mem_singleton _)
  have hfz : f (Ψ 3 * Ψ 3) = Ψ 3 * Ψ 3 := by
    rw [hfx, ← hzH, mul_inv_cancel_right]
  have hS_eq : evalSigned [f (Ψ 3), f (Ψ 16), f (Ψ 17)] sWord = f (Ψ 18) := by
    rw [← sM_eq, map_evalSigned]
    rfl
  have hT_eq : evalSigned [f (Ψ 3), f (Ψ 16), f (Ψ 17)] tWord * (Ψ 3 * Ψ 3) = f (Ψ 19) := by
    rw [← tM_eq, map_mul, hfz, map_evalSigned]
    rfl
  have hrel : ∀ v ∈ szRels, pval (f (Ψ 18)) (f (Ψ 19)) v = 1 := fun v hv => by
    rw [← map_pval, rel_net v hv, map_one]
  have rels : szRelsOK 16240 (p0A ()) (p1A ()) = true := by
    unfold szRelsOK
    rw [List.all_eq_true]
    intro v hv
    refine (eqA_iff (rep_szPwordA rSA (rep_inv' rSA) rTA (rep_inv' rTA) v) rep_idA).2 ?_
    rw [hS_eq, hT_eq]
    exact hrel v hv
  unfold szCoverChk
  simp only [Bool.and_eq_true, and_assoc]
  exact ⟨CertificateChecks.KernelMisc.RuCover.letters_p0,
    CertificateChecks.KernelMisc.RuCover.letters_p1,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep r0,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep r1, hflag,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rM1,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rM2,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rW,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rH,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rL0,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rL1,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rL2,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rSA,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rTA, rels⟩

end Main

end CertificateChecks.KernelMisc.RuCoverNet

end
