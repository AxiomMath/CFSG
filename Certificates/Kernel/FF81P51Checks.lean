module

public import Certificates.Data.Kernel.FF81P51Wit

public section

open CFSG.RankThree.PartTwo.Sec21.FF81.P51 Matrix

namespace Certificates.Kernel.C899051

theorem mem_nonzeroL : ∀ v : V, v ≠ 0 → v ∈ nonzeroL := by decide +kernel
theorem not_zero_mem_nonzeroL : (0 : V) ∉ nonzeroL := by decide +kernel
theorem mem_allV : ∀ v : V, v ∈ allV := by decide +kernel
theorem H0L_transpose : ∀ A ∈ H0L, mm A Aᵀ = 1 ∧ mm Aᵀ A = 1 :=
  forall_mem_of_all (by decide +kernel)
theorem H0L_comm_T0 : ∀ A ∈ H0L, mm A T0 = mm T0 A :=
  forall_mem_of_all (by decide +kernel)
theorem H0L_colsD : ∀ c₀ ∈ E0D, ∀ c₁ ∈ SUD, ∀ c₂ ∈ SUD, ∀ c₃ ∈ SUD,
    c₁ = c₂ ∨ c₁ = c₂.neg ∨ c₁ = c₃ ∨ c₁ = c₃.neg ∨ c₂ = c₃ ∨ c₂ = c₃.neg ∨
      ofColsD c₀ c₁ c₂ c₃ ∈ H0D := by decide +kernel
theorem E0L_eqD : E0L = E0D.map V4.toV := by decide +kernel
theorem SU_eqD : SU = SUD.map V4.toV := by decide +kernel
theorem card_stab : ((H0L.filter fun A => decide (mv A (e 0) = e 0)).toFinset).card = 48 := by
  decide +kernel
theorem tab_spec : ∀ v ∈ nonzeroL, (tab v).2 ∈ H0L ∧ mv (tab v).2 (rep (tab v).1) = v := by
  decide +kernel
theorem tab_rep : ∀ k : Fin 7, (tab (rep k)).1 = k := by decide +kernel
theorem rep_ne_zero : ∀ k : Fin 7, rep k ≠ 0 := by decide +kernel
theorem nonzeroL_eq : nonzeroL = nonzeroD.map V4.toV := by decide +kernel
theorem allV_eq : allV = allD.map V4.toV := by decide +kernel
theorem H0L_eq : H0L = H0D.map M16.toM := by decide +kernel
theorem mem_allD : ∀ x : V4, x ∈ allD := by
  intro x
  cases x with
  | mk a b c d =>
    revert a b c d
    decide +kernel
theorem mem_nonzeroD : ∀ x : V4, x ≠ V4.zero → x ∈ nonzeroD := by
  intro x
  cases x with
  | mk a b c d =>
    revert a b c d
    decide +kernel
theorem tab_eqD : ∀ x ∈ allD, tab x.toV = ((tabD x).1, (tabD x).2.toM) :=
  forall_mem_of_all (by decide +kernel)
theorem rep_eqD : ∀ k : Fin 7, rep k = (repD k).toV := by decide +kernel
theorem okL_eq : ∀ k : Fin 7, okL k = (okLD k).map V4.toV := by decide +kernel
theorem T0_eqD : T0 = T0D.toM := by decide +kernel
theorem S1_eqD : S1 = S1D.toM := by decide +kernel
theorem Tau_eqD : Tau = TauD.toM := by decide +kernel
theorem Cyc_eqD : Cyc = CycD.toM := by decide +kernel
theorem Sig01_eqD : Sig01 = Sig01D.toM := by decide +kernel
theorem e0_eqD : e 0 = e0D.toV := by decide +kernel
theorem H0D_sub_H0WD : ∀ a ∈ H0D, a ∈ H0WD := forall_mem_of_all (by decide +kernel)
theorem okD : ∀ k : Fin 7, ∀ y ∈ allD, V4.dot y (repD k) = 1 → OkBD (repD k) y → y ∈ okLD k := by
  decide +kernel
theorem e0_ne_zero : e 0 ≠ 0 := by decide +kernel
theorem e_ne : ∀ i j : Fin 4, i ≠ j → e i ≠ e j ∧ e i ≠ -e j := by decide +kernel
theorem T0_eq : T0 = 1 + vecMulVec (e 0) (e 0) := by decide +kernel
theorem T0_sq : mm T0 T0 = 1 := by decide +kernel
theorem e0_dot : e 0 ⬝ᵥ e 0 = 1 := by decide +kernel
theorem rep_zero : rep 0 = e 0 := by decide +kernel
theorem vec_e0 : (![1, 0, 0, 0] : V) = e 0 := by decide +kernel
theorem sig01_cyc4 : mm Sig01 Cyc4 ∈ H0L := by decide +kernel
theorem sig01_sq : mm Sig01 Sig01 = 1 := by decide +kernel
theorem sig01_e1 : Sig01 *ᵥ e 1 = e 0 := by decide +kernel
theorem mA_sub_Fr8 : ∀ v ∈ nonzeroL, mA (tab v).1 = true → v ∈ Fr8 := by decide +kernel
theorem mA_e : ∀ j : Fin 4, e j ∈ nonzeroL ∧ mA (tab (e j)).1 = true := by decide +kernel
theorem sig01_Fr8 : ∀ v ∈ Fr8, v ≠ e 1 → v ≠ -e 1 → Sig01 *ᵥ v ∈ SU := by decide +kernel
theorem T0_cols : ofCols ![-e 0, e 1, e 2, e 3] = T0 := by decide +kernel
theorem S1_cols : ofCols ![e 0, -e 1, e 2, e 3] = S1 := by decide +kernel
theorem Tau_cols : ofCols ![e 0, e 2, e 1, e 3] = Tau := by decide +kernel
theorem Cyc_cols : ofCols ![e 0, e 2, e 3, e 1] = Cyc := by decide +kernel
theorem Sig01_cols : Sig01 *ᵥ e 0 = e 1 ∧ Sig01 *ᵥ e 1 = e 0 ∧ Sig01 *ᵥ e 2 = e 2 ∧
    Sig01 *ᵥ e 3 = e 3 := by decide +kernel
theorem Cyc4_cols : Cyc4 *ᵥ e 0 = e 1 ∧ Cyc4 *ᵥ e 1 = e 2 ∧ Cyc4 *ᵥ e 2 = e 3 ∧
    Cyc4 *ᵥ e 3 = e 0 := by decide +kernel
theorem T0_e0 : T0 *ᵥ e 0 = -e 0 := by decide +kernel
theorem rep_six : rep 6 = e 0 + e 1 + e 2 + e 3 := by decide +kernel
theorem e_succ_zero : ∀ i : Fin 4, i ≠ 0 → e i 0 = 0 := by decide +kernel
theorem pos_or : ∀ v ∈ nonzeroL, pos v = true ∨ pos (-v) = true := by decide +kernel
theorem not_pos_and : ∀ v ∈ nonzeroL, ¬(pos v = true ∧ pos (-v) = true) := by decide +kernel
theorem neg_mem_nonzeroL : ∀ v ∈ nonzeroL, -v ∈ nonzeroL := by decide +kernel
theorem lineCount_mA : lineCount mA = 4 := by decide +kernel
theorem lineCount_mB : lineCount mB = 12 := by decide +kernel
theorem lineCount_mC : lineCount mC = 24 := by decide +kernel
theorem lineCount_mD : lineCount mD = 15 := by decide +kernel
theorem lineCount_mE : lineCount mE = 30 := by decide +kernel
theorem vecCount_mA : ((nonzeroL.filter fun v => mA (tab v).1).toFinset).card = 2 * lineCount mA := by
  decide +kernel
theorem vecCount_mB : ((nonzeroL.filter fun v => mB (tab v).1).toFinset).card = 2 * lineCount mB := by
  decide +kernel
theorem vecCount_mC : ((nonzeroL.filter fun v => mC (tab v).1).toFinset).card = 2 * lineCount mC := by
  decide +kernel
theorem vecCount_mD : ((nonzeroL.filter fun v => mD (tab v).1).toFinset).card = 2 * lineCount mD := by
  decide +kernel
theorem vecCount_mE : ((nonzeroL.filter fun v => mE (tab v).1).toFinset).card = 2 * lineCount mE := by
  decide +kernel

theorem fwitsOK_true : fwitsOK cfgsD fwitsD = true := by decide +kernel

end Certificates.Kernel.C899051
