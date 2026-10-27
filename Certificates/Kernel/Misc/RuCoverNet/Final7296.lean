module

public import Certificates.Kernel.Misc.RuCoverNet.Final7295
public import Certificates.Kernel.Misc.RuCoverNet.Checks7296E
public import Certificates.Kernel.Misc.RuCoverNet.Checks7296N
public import CFSG.Certificates.Kernel.Misc.RuCoverNetWSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.CentCoverNative
import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.IntervalCases
import CFSG.Sporadic.Recognition.RuMultiplierInputs
import CFSG.Sporadic.Presentation.RuExactInputs
import CFSG.LieType.Multipliers.CoverWords
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuCoverNet

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.RuCover
  CFSG.EvenSporadicStandard.TwoRu.SzCover CFSG.EvenSporadicStandard.TwoRu.CentCover

local notation "Φ" j:max => CFSG.KC.YModel.Sch.netPerm 14 16240 (CFSG.KD.RuCoverNet7296.V j)
local notation "Ψ" j:max => CFSG.KC.YModel.Sch.netPerm 14 16240 (CFSG.KD.RuCoverNet.U j)

#kc_forall_tree hw7296 (fun i => CFSG.KC.YModel.wordOK 14 6 2 CFSG.KD.RuCoverNet7296.V
  CFSG.KD.RuCoverNet7296.CP CFSG.KD.RuCoverNet7296.CL i = true) 20 CFSG.KD.RuCoverNet7296.ch7296w

#kc_forall_tree hf7296 (fun k => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (facW k) (jW k) = true) 6 CFSG.KD.RuCoverNet7296.ch7296f

#kc_forall_tree hs7296 (fun i => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (fW i ++ fW i) [] = true) 6 CFSG.KD.RuCoverNet7296.ch7296s

#kc_forall_tree hc7296 (fun k => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (fW (k / 6) ++ fW (k % 6)) (fW (k % 6) ++ fW (k / 6)) = true) 36 CFSG.KD.RuCoverNet7296.ch7296c

#kc_forall_tree hm7296 (fun k => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (CFSG.KC.Misc.RuCoverNet.memW k) (etaW 6 (CFSG.KD.RuCoverNet7296.MC k)) = true) 80
  CFSG.KD.RuCoverNet7296.ch7296m

#kc_forall_tree hy7296 (fun i => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (jW 4 ++ fW i) (fW i ++ jW 4) = true) 6 CFSG.KD.RuCoverNet7296.ch7296y

#kc_forall_tree hx7296 (fun i => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (y2W ++ fW i) (fW i ++ y2W) = true) 6 CFSG.KD.RuCoverNet7296.ch7296x

#kc_forall_tree hn7296 (fun c => CFSG.KC.Misc.RuCoverNet.neW CFSG.KD.RuCoverNet7296.V 11 21 0
  (Bool.rec (motive := fun _ => List Int) (etaW 6 c) y5W (Nat.beq c 0)) []
  (CFSG.KD.RuCoverNet7296.NB c) (CFSG.KD.RuCoverNet7296.NX c) (CFSG.KD.RuCoverNet7296.NY c) =
  true) 64 CFSG.KD.RuCoverNet7296.ch7296n

#kc_forall_tree hg7296 (fun k => Bool.rec (motive := fun _ => Bool)
  (CFSG.KC.Misc.RuCoverNet.neW CFSG.KD.RuCoverNet7296.V 11 21 0
    (CFSG.KC.Misc.RuCoverNet.cosU k (CFSG.KD.RuCoverNet7296.KI k))
    (CFSG.KC.Misc.RuCoverNet.cosV k (CFSG.KD.RuCoverNet7296.KI k))
    (CFSG.KD.RuCoverNet7296.KB k) (CFSG.KD.RuCoverNet7296.KX k) (CFSG.KD.RuCoverNet7296.KY k))
  true (Nat.beq (k / 16) (k % 16)) = true) 256 CFSG.KD.RuCoverNet7296.ch7296g

theorem bounds7296 : (∀ k < 80, CFSG.KD.RuCoverNet7296.MC k < 64) ∧
    (∀ c < 64, CFSG.KD.RuCoverNet7296.NB c < 16240) ∧
    (∀ k < 256, CFSG.KD.RuCoverNet7296.KI k < 6 ∧ CFSG.KD.RuCoverNet7296.KB k < 16240) := by
  decide +kernel

theorem letters7296 : (∀ c < 64, lettersOK 2 (etaW 6 c) = true) ∧
    (∀ k < 6, lettersOK 2 (facW k) = true ∧ lettersOK 2 (jW k) = true ∧
      (facTerms k).all (fun t => lettersOK 2 t.1) = true) ∧
    (∀ i < 6, ∀ j < 6, lettersOK 2 (fW i ++ fW j) = true) ∧
    (∀ a < 6, ∀ i < 6, lettersOK 2 (jW a ++ fW i ++ invW (jW a)) = true ∧
      lettersOK 2 (jW a ++ fW i) = true ∧ lettersOK 2 (fW i ++ jW a) = true ∧
      lettersOK 2 (commW (jW a) (jW i)) = true) ∧
    (∀ a < 6, lettersOK 2 (jW a ++ jW a) = true ∧ lettersOK 2 (y2W ++ fW a) = true ∧
      lettersOK 2 (fW a ++ y2W) = true ∧ lettersOK 2 (fW a ++ fW a) = true) ∧
    (∀ s < 16, ∀ t < 16, ∀ i < 6, lettersOK 2 (invW (gW s) ++ gW t ++ fW i) = true ∧
      lettersOK 2 (fW i ++ invW (gW s) ++ gW t) = true) ∧
    lettersOK 2 zW = true ∧ lettersOK 2 y5W = true ∧ lettersOK 2 (commW (jW 4) y2W) = true := by
  decide +kernel

theorem codes7296 :
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 0) (CFSG.KD.RuCoverNet7296.CL 0) = [2, 4] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 1) (CFSG.KD.RuCoverNet7296.CL 1) = [6, 4] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 2) (CFSG.KD.RuCoverNet7296.CL 2) = [6, 8] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 3) (CFSG.KD.RuCoverNet7296.CL 3) = [6, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 4) (CFSG.KD.RuCoverNet7296.CL 4) = [12, 6] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 5) (CFSG.KD.RuCoverNet7296.CL 5) = [14, 8] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 6) (CFSG.KD.RuCoverNet7296.CL 6) = [11] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 7) (CFSG.KD.RuCoverNet7296.CL 7) = [18, 2] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 8) (CFSG.KD.RuCoverNet7296.CL 8) = [20, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 9) (CFSG.KD.RuCoverNet7296.CL 9) = [6, 16] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 10) (CFSG.KD.RuCoverNet7296.CL 10) =
      [24, 24, 24, 24, 24, 24, 24, 24, 24, 24] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 11) (CFSG.KD.RuCoverNet7296.CL 11) =
      [26, 22] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 12) (CFSG.KD.RuCoverNet7296.CL 12) =
      [28, 28, 28, 28, 28, 28] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 13) (CFSG.KD.RuCoverNet7296.CL 13) =
      [14, 14] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 14) (CFSG.KD.RuCoverNet7296.CL 14) = [33] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 15) (CFSG.KD.RuCoverNet7296.CL 15) =
      [34, 22] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 16) (CFSG.KD.RuCoverNet7296.CL 16) =
      [36, 32] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 17) (CFSG.KD.RuCoverNet7296.CL 17) =
      [26, 38] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 18) (CFSG.KD.RuCoverNet7296.CL 18) =
      [40, 40, 40, 40] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 19) (CFSG.KD.RuCoverNet7296.CL 19) =
      [30, 42] := by
  decide +kernel

theorem es23 {G : Type*} [Group G] (g h f : G) : ∀ w : List ℤ, lettersOK 2 w = true →
    evalSigned [g, h] w = evalSigned [g, h, f] w
  | [], _ => rfl
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hl2⟩, hw⟩ := hw
    have hw' : lettersOK 2 w = true := by simpa [lettersOK, List.all_eq_true] using hw
    rw [evalSigned_cons, evalSigned_cons, es23 g h f w hw']
    have e : [g, h].getD (l.natAbs - 1) 1 = [g, h, f].getD (l.natAbs - 1) 1 := by
      rcases (by omega : l.natAbs - 1 = 0 ∨ l.natAbs - 1 = 1) with e | e <;> rw [e] <;> rfl
    rw [e]

theorem lw23 {w : List ℤ} (h : lettersOK 2 w = true) : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 3 := by
  simp only [lettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  exact fun l hl => ⟨(h l hl).1, by have := (h l hl).2; omega⟩

section Main


theorem phi_base : ∀ c < 2, CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet7296.V c) := by
  intro c hc
  interval_cases c
  · exact psi_good hRho (j := 3) (by decide)
  · exact psi_good hRho (j := 4) (by decide)

theorem phi_chain : ∀ j < 22, CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet7296.V j) ∧
    ∀ i, j = 2 + i → Φ j = CFSG.KC.YModel.Sch.cpermL 14 16240 CFSG.KD.RuCoverNet7296.V
      (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP i) (CFSG.KD.RuCoverNet7296.CL i)) :=
  CFSG.KC.Misc.RuCoverNet.chain_spec (E := 20) (by decide) (by decide) phi_base hw7296

theorem phi_good {j : Nat} (hj : j < 22) :
    CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet7296.V j) := (phi_chain j hj).1

theorem phi_val {i : Nat} (hi : i < 20) {cs : List Nat}
    (hc : CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP i)
      (CFSG.KD.RuCoverNet7296.CL i) = cs) :
    Φ (2 + i) = CFSG.KC.YModel.Sch.cpermL 14 16240 CFSG.KD.RuCoverNet7296.V cs := by
  rw [← hc]
  exact (phi_chain (2 + i) (by omega)).2 i rfl

theorem phi0 : Φ 0 = Ψ 3 := rfl

theorem phi1 : Φ 1 = Ψ 4 := rfl

theorem f2 : Φ 2 = Φ 0 * Φ 1 := by
  have h := phi_val (i := 0) (by decide) codes7296.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 0, cperm_ev 1] at h
  exact h

theorem f3 : Φ 3 = Φ 2 * Φ 1 := by
  have h := phi_val (i := 1) (by decide) codes7296.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 2, cperm_ev 1] at h
  exact h

theorem f4 : Φ 4 = Φ 2 * Φ 3 := by
  have h := phi_val (i := 2) (by decide) codes7296.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 2, cperm_ev 3] at h
  exact h

theorem f5 : Φ 5 = Φ 2 * Φ 4 := by
  have h := phi_val (i := 3) (by decide) codes7296.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 2, cperm_ev 4] at h
  exact h

theorem f6 : Φ 6 = Φ 5 * Φ 2 := by
  have h := phi_val (i := 4) (by decide) codes7296.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 5, cperm_ev 2] at h
  exact h

theorem f7 : Φ 7 = Φ 6 * Φ 3 := by
  have h := phi_val (i := 5) (by decide) codes7296.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 6, cperm_ev 3] at h
  exact h

theorem f8 : Φ 8 = (Φ 4)⁻¹ := by
  have h := phi_val (i := 6) (by decide) codes7296.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_nil, mul_one, cperm_od 4] at h
  exact h

theorem f9 : Φ 9 = Φ 8 * Φ 0 := by
  have h := phi_val (i := 7) (by decide) codes7296.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 8, cperm_ev 0] at h
  exact h

theorem f10 : Φ 10 = Φ 9 * Φ 4 := by
  have h := phi_val (i := 8) (by decide) codes7296.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 9, cperm_ev 4] at h
  exact h

theorem f11 : Φ 11 = Φ 2 * Φ 7 := by
  have h := phi_val (i := 9) (by decide) codes7296.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 2, cperm_ev 7] at h
  exact h

theorem f12 : Φ 12 = Φ 11 ^ 10 := by
  have h := phi_val (i := 10) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.1
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 11] at h
  rw [h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem f13 : Φ 13 = Φ 12 * Φ 10 := by
  have h := phi_val (i := 11) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 12, cperm_ev 10] at h
  exact h

theorem f14 : Φ 14 = Φ 13 ^ 6 := by
  have h := phi_val (i := 12) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 13] at h
  rw [h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem f15 : Φ 15 = Φ 6 * Φ 6 := by
  have h := phi_val (i := 13) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 6] at h
  exact h

theorem f16 : Φ 16 = (Φ 15)⁻¹ := by
  have h := phi_val (i := 14) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_nil, mul_one, cperm_od 15] at h
  exact h

theorem f17 : Φ 17 = Φ 16 * Φ 10 := by
  have h := phi_val (i := 15) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 16, cperm_ev 10] at h
  exact h

theorem f18 : Φ 18 = Φ 17 * Φ 15 := by
  have h := phi_val (i := 16) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 17, cperm_ev 15] at h
  exact h

theorem f19 : Φ 19 = Φ 12 * Φ 18 := by
  have h := phi_val (i := 17) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 12, cperm_ev 18] at h
  exact h

theorem f20 : Φ 20 = Φ 19 ^ 4 := by
  have h := phi_val (i := 18) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [cpermL_cons, cpermL_nil, mul_one] at h
  rw [cperm_ev 19] at h
  rw [h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem f21 : Φ 21 = Φ 14 * Φ 20 := by
  have h := phi_val (i := 19) (by decide) codes7296.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 14, cperm_ev 20] at h
  exact h

theorem slotRun_eq7296 : slotRun ruCProg (Φ 0) (Φ 1) = (Φ 11, Φ 21) := by
  rw [f21, f20, f19, f18, f17, f16, f15, f14, f13, f12, f11, f10, f9, f8, f7, f6, f5, f4, f3, f2]
  rfl

theorem evEq {u v : List ℤ} (hu : lettersOK 2 u = true) (hv : lettersOK 2 v = true)
    (h : CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0 u v = true) :
    evalSigned [Φ 11, Φ 21] u = evalSigned [Φ 11, Φ 21] v := by
  rw [es23 _ _ (Φ 0) u hu, es23 _ _ (Φ 0) v hv]
  exact CFSG.KC.Misc.RuCoverNet.eqW_spec (by decide) (by decide) (by decide)
    (phi_good (by decide)) (phi_good (by decide)) (phi_good (by decide)) (lw23 hu) (lw23 hv) h

theorem evNe {u v : List ℤ} {b x y : Nat} (hb : b < 16240) (hu : lettersOK 2 u = true)
    (hv : lettersOK 2 v = true)
    (h : CFSG.KC.Misc.RuCoverNet.neW CFSG.KD.RuCoverNet7296.V 11 21 0 u v b x y = true) :
    evalSigned [Φ 11, Φ 21] u ≠ evalSigned [Φ 11, Φ 21] v := by
  rw [es23 _ _ (Φ 0) u hu, es23 _ _ (Φ 0) v hv]
  exact CFSG.KC.Misc.RuCoverNet.neW_spec (by decide) (by decide) (by decide)
    (phi_good (by decide)) (phi_good (by decide)) (phi_good (by decide)) hb (lw23 hu) (lw23 hv) h

section Tables

variable {tA tB : Array ℕ} (rA : Rep 16240 tA (Φ 11)) (rB : Rep 16240 tB (Φ 21))
include rA rB

theorem ccEqB_of {u v : List ℤ} (hu : lettersOK 2 u = true) (hv : lettersOK 2 v = true)
    (h : CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0 u v = true) :
    ccEqB 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] u v = true := by
  unfold ccEqB
  rw [hu, hv, Bool.true_and, Bool.true_and]
  exact (eqA_iff (rep_wordA2 rA rB u hu) (rep_wordA2 rA rB v hv)).2 (evEq hu hv h)

theorem ccNeB_of {u v : List ℤ} {b x y : Nat} (hb : b < 16240) (hu : lettersOK 2 u = true)
    (hv : lettersOK 2 v = true)
    (h : CFSG.KC.Misc.RuCoverNet.neW CFSG.KD.RuCoverNet7296.V 11 21 0 u v b x y = true) :
    ccNeB 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] u v = true := by
  unfold ccNeB
  rw [hu, hv, Bool.true_and, Bool.true_and, Bool.not_eq_true']
  exact Bool.eq_false_iff.2 fun he =>
    evNe hb hu hv h ((eqA_iff (rep_wordA2 rA rB u hu) (rep_wordA2 rA rB v hv)).1 he)

theorem inEta_of {w : List ℤ} {k : Nat} (hk : k < 80) (hw : lettersOK 2 w = true)
    (hm : CFSG.KC.Misc.RuCoverNet.memW k = w) :
    ccInEta 16240 (ccEtaTab 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB])
      (wordA 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] w) = true := by
  have hc := bounds7296.1 k hk
  have hl := letters7296.1 _ hc
  have h := hm7296 k hk
  rw [hm] at h
  unfold ccInEta ccEtaTab
  rw [List.any_eq_true]
  refine ⟨(CFSG.KD.RuCoverNet7296.MC k, wordA 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB]
    (etaW 6 (CFSG.KD.RuCoverNet7296.MC k))), List.mem_map.2 ⟨_, List.mem_range.2 hc, rfl⟩, ?_⟩
  exact (eqA_iff (rep_wordA2 rA rB w hw) (rep_wordA2 rA rB _ hl)).2 (evEq hw hl h)

end Tables

theorem blt_t {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem blt_f {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · rw [Nat.blt_eq] at e
    omega

theorem memW_a (a i : Nat) (ha : a < 6) (hi : i < 6) :
    CFSG.KC.Misc.RuCoverNet.memW (6 * a + i) = jW a ++ fW i ++ invW (jW a) := by
  have h1 : Nat.blt (6 * a + i) 36 = true := blt_t (by omega)
  have h2 : (6 * a + i) / 6 = a := by omega
  have h3 : (6 * a + i) % 6 = i := by omega
  unfold CFSG.KC.Misc.RuCoverNet.memW
  rw [h1, h2, h3]

theorem memW_b (a : Nat) (ha : a < 6) :
    CFSG.KC.Misc.RuCoverNet.memW (36 + a) = jW a ++ jW a := by
  have h1 : Nat.blt (36 + a) 36 = false := blt_f (by omega)
  have h2 : Nat.blt (36 + a) 42 = true := blt_t (by omega)
  have h3 : 36 + a - 36 = a := by omega
  unfold CFSG.KC.Misc.RuCoverNet.memW
  rw [h1, h2, h3]

theorem memW_c (a b : Nat) (ha : a < 6) (hb : b < 6) :
    CFSG.KC.Misc.RuCoverNet.memW (42 + (6 * a + b)) = commW (jW a) (jW b) := by
  have h1 : Nat.blt (42 + (6 * a + b)) 36 = false := blt_f (by omega)
  have h2 : Nat.blt (42 + (6 * a + b)) 42 = false := blt_f (by omega)
  have h3 : Nat.blt (42 + (6 * a + b)) 78 = true := blt_t (by omega)
  have h4 : (42 + (6 * a + b) - 42) / 6 = a := by omega
  have h5 : (42 + (6 * a + b) - 42) % 6 = b := by omega
  unfold CFSG.KC.Misc.RuCoverNet.memW
  rw [h1, h2, h3, h4, h5]

theorem beq_false {s t : Nat} (h : s ≠ t) : Nat.beq s t = false := by
  cases e : Nat.beq s t
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

section Fam

variable {tA tB : Array ℕ} (rA : Rep 16240 tA (Φ 11)) (rB : Rep 16240 tB (Φ 21))
include rA rB

theorem base_of : ccBase 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] = true := by
    have L := letters7296
    have B := bounds7296
    unfold ccBase
    rw [ccEqB_of rA rB (by decide) (by decide) CFSG.KD.RuCoverNet7296.ch7296b0,
      ccEqB_of rA rB (by decide) (by decide) CFSG.KD.RuCoverNet7296.ch7296b1,
      ccEqB_of rA rB (by decide) (by decide) CFSG.KD.RuCoverNet7296.ch7296b2,
      ccNeB_of rA rB (B.2.1 0 (by decide)) L.2.2.2.2.2.2.2.1 (by decide) (hn7296 0 (by decide))]
    rfl
theorem fac_of : ccFac 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] = true := by
    have L := letters7296
    unfold ccFac
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    rw [ccEqB_of rA rB (L.2.1 k hk).1 (L.2.1 k hk).2.1 (hf7296 k hk), (L.2.1 k hk).2.2]
    rfl
theorem elem_of : ccElem 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] = true := by
    have L := letters7296
    unfold ccElem
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [List.mem_range] at hi
      exact ccEqB_of rA rB (L.2.2.2.2.1 i hi).2.2.2 (by decide) (hs7296 i hi)
    · rw [List.mem_range] at hi
      rw [List.all_eq_true]
      intro j hj
      rw [List.mem_range] at hj
      have h := hc7296 (6 * i + j) (by change 6 * i + j < 36; omega)
      rw [show (6 * i + j) / 6 = i by omega, show (6 * i + j) % 6 = j by omega] at h
      exact ccEqB_of rA rB (L.2.2.1 i hi j hj) (L.2.2.1 j hj i hi) h
omit rA rB in
theorem inEtaAt {T : Array ℕ} {c : Nat} (hc : c < 64)
    (h : eqA 16240 T (wordA 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] (etaW 6 c)) =
      true) :
    ccInEta 16240 (ccEtaTab 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB]) T = true := by
  unfold ccInEta ccEtaTab
  rw [List.any_eq_true]
  exact ⟨(c, wordA 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] (etaW 6 c)),
    List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩, h⟩

theorem grpT : Φ 0 * Φ 0 = evalSigned [Φ 11, Φ 21] (etaW 6 (CFSG.KD.RuCoverNet7296.MC 79)) := by
  have hl := letters7296.1 _ (bounds7296.1 79 (by decide))
  have h := hm7296 79 (by decide)
  have e79 : CFSG.KC.Misc.RuCoverNet.memW 79 = [3, 3] := rfl
  rw [e79] at h
  have e := CFSG.KC.Misc.RuCoverNet.eqW_spec (by decide) (by decide) (by decide)
    (phi_good (by decide)) (phi_good (by decide)) (phi_good (by decide)) (by decide) (lw23 hl) h
  rw [← es23 _ _ (Φ 0) _ hl] at e
  rw [← e]
  simp [evalSigned]

theorem inEtaT_of {t0 : Array ℕ} (r0 : Rep 16240 t0 (Φ 0)) :
    ccInEta 16240 (ccEtaTab 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB])
      (compA 16240 t0 t0) = true := by
  have hc := bounds7296.1 79 (by decide)
  have hl := letters7296.1 _ hc
  have key : eqA 16240 (compA 16240 t0 t0) (wordA 16240 #[tA, tB]
      #[invCand 16240 tA, invCand 16240 tB] (etaW 6 (CFSG.KD.RuCoverNet7296.MC 79))) = true :=
    (eqA_iff (rep_compA r0 r0) (rep_wordA2 rA rB _ hl)).2 (grpT rA rB)
  exact inEtaAt hc key

theorem eta_of {t0 : Array ℕ} (r0 : Rep 16240 t0 (Φ 0)) :
    ccEta 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB]
      (ccEtaTab 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB]) (compA 16240 t0 t0) =
      true := by
    have L := letters7296
    have B := bounds7296
    unfold ccEta
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨⟨⟨L.1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro p hp
      unfold ccEtaTab at hp
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
      rw [List.mem_range] at hc
      by_cases h0 : c = 0
      · subst h0
        rfl
      · have hn := hn7296 c hc
        rw [beq_false h0] at hn
        have hne : eqA 16240 (wordA 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB]
            (etaW 6 c)) (idA 16240) = false :=
          Bool.eq_false_iff.2 fun he => evNe (B.2.1 c hc) (L.1 c hc) (by decide) hn
            ((eqA_iff (rep_wordA2 rA rB _ (L.1 c hc)) rep_idA).1 he)
        simp only [hne, Bool.not_false, Bool.or_true]
    · intro k hk i hi
      unfold ccWordInEta
      rw [(L.2.2.2.1 k hk i hi).1, Bool.true_and]
      exact inEta_of rA rB (k := 6 * k + i) (by omega) (L.2.2.2.1 k hk i hi).1 (memW_a k i hk hi)
    · intro a ha
      unfold ccWordInEta
      rw [(L.2.2.2.2.1 a ha).1, Bool.true_and]
      exact inEta_of rA rB (k := 36 + a) (by omega) (L.2.2.2.2.1 a ha).1 (memW_b a ha)
    · intro a ha b hb
      unfold ccWordInEta
      rw [(L.2.2.2.1 a ha b hb).2.2.2, Bool.true_and]
      exact inEta_of rA rB (k := 42 + (6 * a + b)) (by omega) (L.2.2.2.1 a ha b hb).2.2.2
        (memW_c a b ha hb)
    · unfold ccWordInEta
      rw [L.2.2.2.2.2.2.1, Bool.true_and]
      exact inEta_of rA rB (k := 78) (by decide) L.2.2.2.2.2.2.1 rfl
    · exact inEtaT_of rA rB r0
theorem cos_of : ccCosets 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] = true := by
    have L := letters7296
    have B := bounds7296
    unfold ccCosets
    rw [List.all_eq_true]
    intro s hs
    rw [List.mem_range] at hs
    rw [List.all_eq_true]
    intro t ht
    rw [List.mem_range] at ht
    rw [Bool.or_eq_true]
    by_cases hst : s = t
    · left
      simp [hst]
    · right
      have hk : 16 * s + t < 256 := by omega
      have h1 : (16 * s + t) / 16 = s := by omega
      have h2 : (16 * s + t) % 16 = t := by omega
      have hg := hg7296 (16 * s + t) hk
      rw [h1, h2, beq_false hst] at hg
      unfold CFSG.KC.Misc.RuCoverNet.cosU CFSG.KC.Misc.RuCoverNet.cosV at hg
      rw [h1, h2] at hg
      rw [List.any_eq_true]
      have hi := (B.2.2 _ hk).1
      refine ⟨CFSG.KD.RuCoverNet7296.KI (16 * s + t), List.mem_range.2 hi, ?_⟩
      exact ccNeB_of rA rB (B.2.2 _ hk).2 (L.2.2.2.2.2.1 s hs t ht _ hi).1
        (L.2.2.2.2.2.1 s hs t ht _ hi).2 hg
theorem yy_of : ccY 16240 #[tA, tB] #[invCand 16240 tA, invCand 16240 tB] = true := by
    have L := letters7296
    unfold ccY
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
    · exact ccEqB_of rA rB (L.2.2.2.1 4 (by decide) i hi).2.1 (L.2.2.2.1 4 (by decide) i hi).2.2.1
        (hy7296 i hi)
    · exact ccEqB_of rA rB (L.2.2.2.2.1 i hi).2.1 (L.2.2.2.2.1 i hi).2.2.1 (hx7296 i hi)
    · exact ccEqB_of rA rB L.2.2.2.2.2.2.2.2 L.2.2.2.2.2.2.1 CFSG.KD.RuCoverNet7296.ch7296z0

end Fam

theorem ccChk_true : ccChk () = true := by
  have r0 : Rep 16240 (p0A ()) (Φ 0) := rep_p0
  have r1 : Rep 16240 (p1A ()) (Φ 1) := rep_p1
  have hflag := slotRunA_flag (n := 16240) ruCProg r0 r1
  have hm := rep_slotRunA ruCProg r0 r1 hflag
  rw [slotRun_eq7296] at hm
  have rA : Rep 16240 (slotRunA 16240 ruCProg (p0A ()) (p1A ())).1 (Φ 11) := hm.1
  have rB : Rep 16240 (slotRunA 16240 ruCProg (p0A ()) (p1A ())).2.1 (Φ 21) := hm.2
  unfold ccChk ccChkAt
  simp only [Bool.and_eq_true, and_assoc]
  exact ⟨CertificateChecks.KernelMisc.RuCover.letters_p1,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep r0,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep r1, hflag,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rA,
    CertificateChecks.KernelCosetJ.RhoPerm.isInvA_of_rep rB, base_of rA rB, fac_of rA rB,
    elem_of rA rB, eta_of rA rB r0, cos_of rA rB, yy_of rA rB⟩

end Main

end CertificateChecks.KernelMisc.RuCoverNet

end
