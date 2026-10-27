module

public import CFSG.Certificates.Kernel.L34M64.TwinSound
public import Certificates.Kernel.L34M64.Mats
public import Certificates.Kernel.L34M64.Lists

public section

namespace CertificateChecks.KernelL34M64

open CFSG.KC.L34M64 CFSG.KD.L34M64 CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H.Mathieu CFSG.Fischer

theorem forall_lt_four {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ t < 4, P t := by
  intro t ht
  interval_cases t <;> assumption

theorem mat_eq {R : Matrix (Fin 8) (Fin 8) F4} {P : ℕ} {L : List ℕ} (h : matChk R P L = true) :
    colsN64 (codes8 R) = L := by
  simp only [matChk, Bool.and_eq_true] at h
  have hR := codesChk_spec h.1
  have e : actH8 R = actP P := funext fun m => (actP_eq hR m).symm
  rw [colsN64_eq (rep8_codes8 R), colsChk_spec h.2, e]

theorem lens : X12.length = 4 ∧ X13.length = 4 ∧ X23.length = 4 ∧
    CFSG.KD.L34M64.U.length = 64 := by
  have h := ch7241len
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem tab_eq {f : ℕ → List ℕ} {T : List (List ℕ)} (hT : T.length = 4)
    (h : ∀ t < 4, f t = T.getD t []) : (List.range 4).map f = T := by
  refine List.ext_getElem (by simp [hT]) fun t h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem T [] h2]
  exact h t (by simpa using h1)

theorem tabX12_eq : tabX12_64 = X12 :=
  tab_eq lens.1 (forall_lt_four (P := fun t =>
      colsN64 (codes8 (adM (um (f4c t) 0 0) (um (f4c t) 0 0))) = X12.getD t [])
    (mat_eq ch7241x12_0) (mat_eq ch7241x12_1) (mat_eq ch7241x12_2) (mat_eq ch7241x12_3))

theorem tabX13_eq : tabX13_64 = X13 :=
  tab_eq lens.2.1 (forall_lt_four (P := fun t =>
      colsN64 (codes8 (adM (um 0 (f4c t) 0) (um 0 (f4c t) 0))) = X13.getD t [])
    (mat_eq ch7241x13_0) (mat_eq ch7241x13_1) (mat_eq ch7241x13_2) (mat_eq ch7241x13_3))

theorem tabX23_eq : tabX23_64 = X23 :=
  tab_eq lens.2.2.1 (forall_lt_four (P := fun t =>
      colsN64 (codes8 (adM (um 0 0 (f4c t)) (um 0 0 (f4c t)))) = X23.getD t [])
    (mat_eq ch7241x23_0) (mat_eq ch7241x23_1) (mat_eq ch7241x23_2) (mat_eq ch7241x23_3))

theorem fldC64_eqD : fldC64 = FLD := by
  rw [colsChk_spec ch7241fld]
  simp only [fldC64, matOf, fldN64_eq, fldP_eq]

theorem grC64_eqD : grC64 = GR := by
  rw [grC64]
  exact mat_eq ch7241gm

theorem tabU64_eqD : tabU64 = CFSG.KD.L34M64.U := by
  have h := ch7241u
  rw [beq_iff_eq] at h
  rw [h, tabU64, tabX12_eq, tabX13_eq, tabX23_eq]
  simp only [compK_eq]

theorem outC64_getD {f t : ℕ} (hf : f < 2) (ht : t < 2) :
    outC64 f t = [idC64, fldC64, grC64, comp fldC64 grC64].getD (f + 2 * t) [] := by
  interval_cases f <;> interval_cases t <;> rfl

theorem outC64_eqD {f t : ℕ} (hf : f < 2) (ht : t < 2) : outC64 f t = OUT.getD (f + 2 * t) [] := by
  have h := ch7241out
  rw [beq_iff_eq] at h
  rw [h, outC64_getD hf ht, fldC64_eqD, grC64_eqD, compK_eq]

theorem cols_eq : (List.range 256).map cols64 = COLS := by
  have h := ch7241cols
  rw [beq_iff_eq] at h
  rw [h]
  refine List.map_congr_left fun p _ => ?_
  change comp (tabU64.getD (p % 64) []) (outC64 (p / 64 % 2) (p / 128 % 2)) = _
  rw [tabU64_eqD, outC64_eqD (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)),
    compK_eq]

theorem dat_eq : dat64 = DAT := by
  have h := ch7241dat
  rw [beq_iff_eq] at h
  rw [h, dat64, cols_eq, isInvK_eq]
  simp only [pickWitK_eq]

theorem chk64_true : chk64 = true := by
  rw [chk64, dat_eq, ← chk1K_eq]
  exact ch7241k1

end CertificateChecks.KernelL34M64
