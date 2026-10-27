module

public import Certificates.Kernel.Sporadic.M22Alt.Check
public import CFSG.Certificates.Kernel.Spor.MCountProved
public import CFSG.Sporadic.Schreier.M22Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.Sporadic.Schreier.M11Data

public section

namespace CertificateChecks.KernelSpor.M22Alt

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.KS CFSG.KS.MEnum CFSG.KS.M11

set_option maxRecDepth 100000

theorem tA_eq : tA = imageList m22gA := by decide

theorem tB_eq : tB = imageList m22gB := by decide

theorem W_eq : W = [[1], [2]] ++ m22Words.map (List.map shiftLabel) := by decide

theorem hc : ∀ i < [22, 21, 20, 16, 3].headD 0 * 3, mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 i 4 11 Rs = CS.getD i 0 := by
  intro i hi
  change i < 66 at hi
  interval_cases i
  exacts [Nat.eq_of_beq_eq_true c0, Nat.eq_of_beq_eq_true c1, Nat.eq_of_beq_eq_true c2, Nat.eq_of_beq_eq_true c3, Nat.eq_of_beq_eq_true c4, Nat.eq_of_beq_eq_true c5, Nat.eq_of_beq_eq_true c6, Nat.eq_of_beq_eq_true c7, Nat.eq_of_beq_eq_true c8, Nat.eq_of_beq_eq_true c9, Nat.eq_of_beq_eq_true c10, Nat.eq_of_beq_eq_true c11, Nat.eq_of_beq_eq_true c12, Nat.eq_of_beq_eq_true c13, Nat.eq_of_beq_eq_true c14, Nat.eq_of_beq_eq_true c15, Nat.eq_of_beq_eq_true c16, Nat.eq_of_beq_eq_true c17, Nat.eq_of_beq_eq_true c18, Nat.eq_of_beq_eq_true c19, Nat.eq_of_beq_eq_true c20, Nat.eq_of_beq_eq_true c21, Nat.eq_of_beq_eq_true c22, Nat.eq_of_beq_eq_true c23, Nat.eq_of_beq_eq_true c24, Nat.eq_of_beq_eq_true c25, Nat.eq_of_beq_eq_true c26, Nat.eq_of_beq_eq_true c27, Nat.eq_of_beq_eq_true c28, Nat.eq_of_beq_eq_true c29, Nat.eq_of_beq_eq_true c30, Nat.eq_of_beq_eq_true c31, Nat.eq_of_beq_eq_true c32, Nat.eq_of_beq_eq_true c33, Nat.eq_of_beq_eq_true c34, Nat.eq_of_beq_eq_true c35, Nat.eq_of_beq_eq_true c36, Nat.eq_of_beq_eq_true c37, Nat.eq_of_beq_eq_true c38, Nat.eq_of_beq_eq_true c39, Nat.eq_of_beq_eq_true c40, Nat.eq_of_beq_eq_true c41, Nat.eq_of_beq_eq_true c42, Nat.eq_of_beq_eq_true c43, Nat.eq_of_beq_eq_true c44, Nat.eq_of_beq_eq_true c45, Nat.eq_of_beq_eq_true c46, Nat.eq_of_beq_eq_true c47, Nat.eq_of_beq_eq_true c48, Nat.eq_of_beq_eq_true c49, Nat.eq_of_beq_eq_true c50, Nat.eq_of_beq_eq_true c51, Nat.eq_of_beq_eq_true c52, Nat.eq_of_beq_eq_true c53, Nat.eq_of_beq_eq_true c54, Nat.eq_of_beq_eq_true c55, Nat.eq_of_beq_eq_true c56, Nat.eq_of_beq_eq_true c57, Nat.eq_of_beq_eq_true c58, Nat.eq_of_beq_eq_true c59, Nat.eq_of_beq_eq_true c60, Nat.eq_of_beq_eq_true c61, Nat.eq_of_beq_eq_true c62, Nat.eq_of_beq_eq_true c63, Nat.eq_of_beq_eq_true c64, Nat.eq_of_beq_eq_true c65]

theorem hRs : Rs = CL.map fun d => (d.2.2.1, pinvS 22 5 (mask 5) d.2.2.1) := by
  decide +kernel

theorem hmem : ∀ j < CL.length, cntSum CS (3 + 2 * j) = 1 := by decide +kernel

theorem nX : cntSum CS 0 = 1155 := by decide +kernel

theorem nY : cntSum CS 1 = 41580 := by decide +kernel

theorem nS : Nat.beq (clsSize CL) (cntSum CS 0) = true := by quickRfl

theorem tot : clsTotR CL CS = 1774080 := by
  decide +kernel

theorem counts : (m22Certificate.check = true)
    ∧ (ordTest 22 2 (toTable m22gA) = true ∧ ordTest 22 4 (toTable m22gB) = true ∧
      pairTest 22 11 6 2 4 (toTable m22gA) (toTable m22gB) = true)
    ∧ ((orderTables m22Certificate 2).length = 1155 ∧
      (orderTables m22Certificate 4).length = 41580)
    ∧ (classOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (orderTables m22Certificate 2) 2000 = true ∧
      classTotal 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (orderTables m22Certificate 2) (orderTables m22Certificate 4) 2000 11 6 2 4 =
        1774080) := by
  have h := mCntZ_sound_proved (gA := m22gA) (gB := m22gB) (words := m22Words) (hn := by decide)
    (bv := #v[0, 1, 2, 3, 4]) (hbs := by decide) (cap := 2000) (sub := 3) tA_eq tB_eq W_eq
    (by decide) rfl base rfl ⟨by decide, by decide⟩ (by decide) (Or.inr rfl) (by norm_num) rfl
    (by decide +kernel) hc hRs hmem (Nat.eq_of_beq_eq_true oA) (Nat.eq_of_beq_eq_true oB) pAB cls
    disj (Nat.eq_of_beq_eq_true nS) (by norm_num) (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, ⟨h2, h3, h4⟩, ⟨h5.trans nX, h6.trans nY⟩, h7, h8.trans tot⟩

end CertificateChecks.KernelSpor.M22Alt

end
