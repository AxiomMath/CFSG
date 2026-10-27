
module

public import CFSG.Certificates.Kernel.SporSch.HNArrMat
public import Certificates.Kernel.SporSch.HN.Strong

public section

namespace CertificateChecks.KernelSporSch.HNArrS

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native CFSG.Sporadic.He.Native
open CFSG.Sporadic.He CertificateChecks.KernelSporSch Matrix

theorem prog_lt : ∀ t ∈ Data.subgroupProgram, t.1 < 11 ∧ t.2.1 < 11 ∧ t.2.2 < 11 := by decide

noncomputable abbrev hJ1 : JH := runProg initJ Data.subgroupProgram 1

noncomputable abbrev hJ2 : JH := runProg initJ Data.subgroupProgram 2

noncomputable abbrev sL (j : ℕ) : JH := sJ LocalData.strongWords hJ1 hJ2 j

noncomputable abbrev SJ : Array (Array ℕ) := Array.ofFn (n := 17) fun j => arrJ (sL j)

theorem regs_get {k : ℕ} (hk : k < 11) :
    (progRegs nPts (initRegs nPts (arrJ aJ) (arrJ bJ)) Data.subgroupProgram)[k]! =
      arrJ (runProg initJ Data.subgroupProgram k) :=
  (progRegs_arrJ _ _ _ prog_lt (initRegs_get rfl rfl).1 (initRegs_get rfl rfl).2).2 k hk

theorem words_lt (j : ℕ) (h2 : 2 ≤ j) (h17 : j < 17) :
    ∀ l ∈ LocalData.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j :=
  (HNStrong.words_ok h2 h17).1

theorem hS_eq : extendStrong nPts #[arrJ hJ1, arrJ hJ2] LocalData.strongWords = SJ :=
  extendStrong_arrJ HNStrong.strong_parts.1 (by omega) words_lt

theorem sL0 : sL 0 = hJ1 := by rw [sL, sJ, ite_eq_left rfl]

theorem sL1 : sL 1 = hJ2 := by rw [sL, sJ, ite_eq_right (by omega), ite_eq_left rfl]

theorem SJ_get {j : ℕ} (hj : j < 17) : SJ[j]! = arrJ (sL j) := strong_get hj

theorem SJ_arrs : ArrsOK 17 SJ (pinvs nPts SJ) sL := strong_arrs

theorem SA_get {j : ℕ} (hj : j < 17) : HNStrong.SA[j]! = HNStrong.F j :=
  ofFn_getElem! (F := HNStrong.F) hj

theorem SIA_get {j : ℕ} (hj : j < 17) : HNStrong.SIA[j]! = HNStrong.FI j :=
  ofFn_getElem! (F := HNStrong.FI) hj

theorem mat_sL : ∀ j < 17,
    matJ (sL j) = toMat 5 133 (HNStrong.F j) ∧ matJ (sL j)⁻¹ = toMat 5 133 (HNStrong.FI j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hm : matJ (sL j) = toMat 5 133 (HNStrong.F j) := by
      rcases Nat.lt_or_ge j 2 with h | h
      · interval_cases j
        · rw [sL0, runProg_mat prog_lt (k := 1) (by omega), HNStrong.regs_12.1]
        · rw [sL1, runProg_mat prog_lt (k := 2) (by omega), HNStrong.regs_12.2]
      · obtain ⟨hl, hw⟩ := HNStrong.words_ok h hj
        rw [sL, sJ_two h hl, ← hw]
        refine (mword_mat (m := j) (fun i hi => ?_) _ hl).symm
        rw [SA_get (by omega), SIA_get (by omega)]
        exact ⟨(ih i hi (by omega)).1.symm, (ih i hi (by omega)).2.symm⟩
    refine ⟨hm, (mat_inv_of_mul ?_).symm⟩
    rw [hm, ← toMat_mulM, toMat_eq_of_beq (HNStrong.F_mul_FI hj), toMat_idM]

end CertificateChecks.KernelSporSch.HNArrS

end
