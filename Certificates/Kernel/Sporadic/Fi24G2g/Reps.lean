
module

public import Certificates.Kernel.Sporadic.Fi24G2g.Pt
public import Certificates.Kernel.Sporadic.Fi24G2e.Reps
public import CFSG.Sporadic.FischerOddCore.Fi23Cent
public import CFSG.Sporadic.FischerOddCore.Fi24Act
public import CFSG.Sporadic.FischerOddCore.Fi24G2dFacts
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Sporadic.Fi24.Ext
public import CFSG.Sporadic.Fi24.ExtOuter
public import CFSG.Sporadic.FischerOddCore.Fi24Stab
public import CFSG.Sporadic.FischerOddCore.Fi24WitCheckBase

public section

namespace CertificateChecks.KernelFi24G2g

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix CertificateChecks.KernelFi24Orb
  CertificateChecks.KernelFi24Ext CertificateChecks.KernelFi24G2e TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge

open CFSG.Sporadic.Fi24 (R tR)
open CFSG.Sporadic.FischerOddCore (fi23ToR fi23U2 fi23U3 rep7)
open CFSG.KD.Fi24G2e (REP CWL GWL GCL nO)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev uA0 : GL (Fin 781) (ZMod 3) := (fi23ToR CFSG.Sporadic.Fi23.a : R)

noncomputable abbrev uB1 : GL (Fin 781) (ZMod 3) := (fi23ToR CFSG.Sporadic.Fi23.b : R)

theorem val_uA0 : (uA0 : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt CFSG.KD.Fi24Ext.H0 := by
  rw [uA0, CFSG.Sporadic.FischerOddCore.fi23ToR_a, CFSG.Sporadic.Fi24.coe_jR]
  change CFSG.Sporadic.Fi24.mat (CFSG.Sporadic.Fi24.extWord CFSG.Sporadic.Fi24.Native.localWords[0]!) = _
  rw [← (CFSG.Sporadic.Fi24.letterOK_localWord (i := 0) (by norm_num)).mat]
  exact H_facts.1.2

theorem val_uB1 : (uB1 : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt CFSG.KD.Fi24Ext.H1 := by
  rw [uB1, CFSG.Sporadic.FischerOddCore.fi23ToR_b, CFSG.Sporadic.Fi24.coe_jR]
  change CFSG.Sporadic.Fi24.mat (CFSG.Sporadic.Fi24.extWord CFSG.Sporadic.Fi24.Native.localWords[1]!) = _
  rw [← (CFSG.Sporadic.Fi24.letterOK_localWord (i := 1) (by norm_num)).mat]
  exact H_facts.2.2

theorem uA0_sq : uA0 * uA0 = 1 := by
  apply Units.ext
  rw [Units.val_mul, val_uA0, Units.val_one]
  exact rep_mats.1

theorem uB1_cube : uB1 * (uB1 * uB1) = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_uB1, Units.val_one]
  exact rep_mats.2.1

@[expose] noncomputable def hu (c : ℕ) : GL (Fin 781) (ZMod 3) :=
  if c = 1 then uA0 else if c = 2 then uB1 else uB1 * uB1

theorem val_hu (c : ℕ) : ((hu c : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
    hm c := by
  unfold hu hm
  split_ifs
  · exact val_uA0
  · exact val_uB1
  · rw [Units.val_mul, val_uB1]

@[expose] def code (z : ℤ) : ℕ := if z = 1 ∨ z = -1 then 1 else if z = 2 then 2 else 3

noncomputable abbrev φ : CFSG.Sporadic.Fi23.J →* GL (Fin 781) (ZMod 3) := R.subtype.comp fi23ToR

theorem φ_genG (z : ℤ) : φ (CFSG.Sporadic.Fi23.genG z) = hu (code z) := by
  have hAi : uA0⁻¹ = uA0 := inv_eq_of_mul_eq_one_right uA0_sq
  have hBi : uB1⁻¹ = uB1 * uB1 := inv_eq_of_mul_eq_one_right uB1_cube
  unfold CFSG.Sporadic.Fi23.genG code hu
  by_cases h1 : z = 1
  · subst h1
    simp
  · by_cases h2 : z = -1
    · subst h2
      simp only [show (-1 : ℤ) ≠ 1 by decide, ↓reduceIte, or_true, map_inv]
      exact hAi
    · by_cases h3 : z = 2
      · subst h3
        simp
      · simp only [h1, h2, h3, ↓reduceIte, or_self, map_inv, show (3 : ℕ) ≠ 1 by decide,
          show (3 : ℕ) ≠ 2 by decide]
        exact hBi

theorem φ_wordG (w : List ℤ) :
    φ (CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG w) = ((w.map code).map hu).prod := by
  unfold CFSG.Sporadic.Th.wordG
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun z _ => φ_genG z

theorem val_prod_hu (l : List ℕ) :
    (((l.map hu).prod : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      (l.map hm).prod := by
  induction l with
  | nil => simp
  | cons c l ih => rw [List.map_cons, List.prod_cons, Units.val_mul, ih, val_hu, List.map_cons,
      List.prod_cons]

theorem dLetters_code : (CFSG.Sporadic.Fi23.Native.dLetters ()).map code =
    [1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2] := by decide

theorem wordW_code : CFSG.Sporadic.FischerOddCore.fi23WordW.map code = [2, 2, 1, 2, 2, 1, 2] := by
  decide

theorem φ_d : (φ CFSG.Sporadic.Fi23.d : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (REP 0) := by
  rw [rep_mats.2.2.1, CFSG.Sporadic.Fi23.d, ← CFSG.Sporadic.Fi23.wordG_dLetters, map_pow,
    φ_wordG, dLetters_code, Units.val_pow_eq_pow_val, val_prod_hu]

theorem φ_W : (φ (CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG
    CFSG.Sporadic.FischerOddCore.fi23WordW) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      (([2, 2, 1, 2, 2, 1, 2] : List ℕ).map hm).prod := by
  rw [φ_wordG, wordW_code, val_prod_hu]

theorem φ_Wi : (((φ (CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi23.genG
    CFSG.Sporadic.FischerOddCore.fi23WordW))⁻¹ : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      (([3, 1, 3, 3, 1, 3, 3] : List ℕ).map hm).prod := by
  have hAi : uA0⁻¹ = uA0 := inv_eq_of_mul_eq_one_right uA0_sq
  have hBi : uB1⁻¹ = uB1 * uB1 := inv_eq_of_mul_eq_one_right uB1_cube
  have hBBi : (uB1 * uB1)⁻¹ = uB1 := by
    rw [mul_inv_rev, hBi]
    calc uB1 * uB1 * (uB1 * uB1) = uB1 * (uB1 * (uB1 * uB1)) := by group
      _ = uB1 := by rw [uB1_cube, mul_one]
  have hu1 : hu 1 = uA0 := by simp [hu]
  have hu2 : hu 2 = uB1 := by simp [hu]
  have hu3 : hu 3 = uB1 * uB1 := by simp [hu]
  rw [φ_wordG, wordW_code, ← val_prod_hu]
  refine congrArg (fun u : GL (Fin 781) (ZMod 3) => (u : Matrix (Fin 781) (Fin 781) (ZMod 3))) ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hu1, hu2, hu3,
    mul_inv_rev, hAi, hBi, mul_assoc]

theorem coe_tR_val : (((tR : R) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
    Mt CFSG.KD.Fi24Ext.T := by
  change CFSG.Sporadic.Fi24.mT = _
  exact mT_eq

theorem val_rep7 {i : ℕ} (hi : i < 7) :
    (((rep7 i : R) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      Mt (REP i) := by
  obtain ⟨-, -, e0, e1, e2, e3, e4, e5, e6⟩ := rep_mats
  have hd : (((fi23ToR CFSG.Sporadic.Fi23.d : R) : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (REP 0) := φ_d
  have hu2 : (((fi23ToR fi23U2 : R) : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (REP 1) := by
    change ((φ fi23U2 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = _
    rw [e1, fi23U2, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul, φ_d,
      φ_genG, φ_genG]
    have h1 : ((hu (code 1) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
        Mt CFSG.KD.Fi24Ext.H0 := by rw [val_hu]; rfl
    have h2 : ((hu (code (-1)) : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
        Mt CFSG.KD.Fi24Ext.H0 := by rw [val_hu]; rfl
    rw [h1, h2]
  have hu3 : (((fi23ToR fi23U3 : R) : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (REP 2) := by
    change ((φ fi23U3 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = _
    rw [e2, fi23U3, map_mul, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      Units.val_mul, φ_d, φ_W, φ_Wi]
    rw [show ((φ fi23U2 : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) =
      Mt (REP 1) from hu2]
  interval_cases i
  · exact hd
  · exact hu2
  · exact hu3
  · rw [e3]
    exact coe_tR_val
  · change ((((fi23ToR CFSG.Sporadic.Fi23.d * tR : R)) : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3)) = _
    rw [Subgroup.coe_mul, Units.val_mul, hd, coe_tR_val, e4, e0]
  · change ((((fi23ToR fi23U2 * tR : R)) : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3)) = _
    rw [Subgroup.coe_mul, Units.val_mul, hu2, coe_tR_val, e5]
  · change ((((fi23ToR fi23U3 * tR : R)) : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3)) = _
    rw [Subgroup.coe_mul, Units.val_mul, hu3, coe_tR_val, e6]

theorem conj_rep7 {i : ℕ} (hi : i < 7) :
    ∃ c : R, c * rep7 i * c⁻¹ = ρ (wp (CWL i)) := by
  refine ⟨(ρ (wp (GCL i)))⁻¹ * (rep7 i * ρ (wp (GWL i))) ^ ((nO i - 1) / 2), ?_⟩
  apply Subtype.ext
  have h := conj_rep_cw hi _ (val_rep7 hi)
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, coe_ρ] using h

end CertificateChecks.KernelFi24G2g

end
