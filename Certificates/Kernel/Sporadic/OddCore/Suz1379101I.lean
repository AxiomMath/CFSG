module

import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Kernel.Sporadic.OddCore.Suz1379101F

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S1379101

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.Sporadic.SuzOddCore.SylowFacts CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

theorem sel10_lt {j : Nat} (h : j < 4) : kOne.sel10 j = RG j := by
  unfold kOne.sel10
  rw [show Nat.blt j 4 = true from Nat.blt_eq.mpr h]

theorem sel10_ge {j : Nat} (h : ¬ j < 4) : kOne.sel10 j = CW (j - 4) := by
  unfold kOne.sel10
  rw [show Nat.blt j 4 = false from Bool.eq_false_iff.2 fun e' => h (Nat.blt_eq.mp e')]
  rfl

theorem sel10_ok {j : Nat} (hj : j < 10) : ok (kOne.sel10 j) = true := by
  by_cases h : j < 4
  · rw [sel10_lt h]
    exact (rA_facts h).2
  · rw [sel10_ge h]
    exact (c_facts (by omega)).2

theorem ten_bind : (tenArrs (rArrs ()) (cArrs ())).size = 10 ∧
    ∀ j < 10, (tenArrs (rArrs ()) (cArrs ()))[j]! = unpack 1782 11 (kOne.sel10 j) := by
  refine ⟨by unfold tenArrs; simp, fun j hj => ?_⟩
  unfold tenArrs
  rw [ofFn_get _ hj]
  simp only
  by_cases h : j < 4
  · rw [if_pos h, (rA_facts h).1, sel10_lt h]
  · rw [if_neg h, (c_facts (by omega)).1, sel10_ge h]

theorem kw_parts : lettersK 10 WA = true ∧ lettersK 10 WB = true ∧
    wordK 1782 11 (mask 11) e kOne.sel10 (fun j => pinv (kOne.sel10 j)) WA = TRI 0 ∧
    wordK 1782 11 (mask 11) e kOne.sel10 (fun j => pinv (kOne.sel10 j)) WB = TRI 1 := by
  have h : (lettersK 10 WA && (lettersK 10 WB &&
      (Nat.beq (wordK 1782 11 (mask 11) e kOne.sel10 (fun j => pinv (kOne.sel10 j)) WA) (TRI 0) &&
        Nat.beq (wordK 1782 11 (mask 11) e kOne.sel10 (fun j => pinv (kOne.sel10 j)) WB)
          (TRI 1)))) = true := kOne2
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1, Nat.eq_of_beq_eq_true h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem genCheck_ok : genCheck (rArrs ()) (cArrs ()) waWord wbWord = true := by
  unfold genCheck
  dsimp only
  obtain ⟨la, lb, wa, wb⟩ := kw_parts
  have hp : ∀ j < 10, CFSG.KC.Enum.permOK 1782 11 (mask 11) (1782 * 11) (kOne.sel10 j)
      (pinv (kOne.sel10 j)) = true := fun j hj => (ok_spec (sel10_ok hj)).2.2
  have hi : (tenArrs (rArrs ()) (cArrs ())).map (invCand 1782) =
      rawInvs 1782 (tenArrs (rArrs ()) (cArrs ())) := rfl
  have c0 : Cn (TRI 0) := by
    have h := kTriAll 0 (by decide)
    unfold kTri at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have c1 : Cn (TRI 1) := by
    have h := kTriAll 1 (by decide)
    unfold kTri at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have ea := S26990.word_of ten_bind hp la
  have eb := S26990.word_of ten_bind hp lb
  rw [hi, waWord_eq, wbWord_eq, ea, eb]
  rw [show wordK 1782 11 (mask 11) S26990.e kOne.sel10 (fun j => pinv (kOne.sel10 j)) WA = TRI 0
      from wa, show wordK 1782 11 (mask 11) S26990.e kOne.sel10 (fun j => pinv (kOne.sel10 j)) WB =
      TRI 1 from wb, Suz2306.b0Arr_eq, Suz2306.b1Arr_eq, ← tri0, ← tri1, S26990.eqA_u c0 c0,
    S26990.eqA_u c1 c1, Nat.beq_refl, Nat.beq_refl]
  rfl

theorem c3T : allN 64 (fun t => canonK 1782 11 (mask 11) (1782 * 11) (N3T t)) = true := by
  decide +kernel

theorem ofFn_range {α : Type} (n : Nat) (g : Nat → α) :
    List.ofFn (fun i : Fin n => g i.val) = (List.range n).map g := by
  apply List.ext_getElem <;> simp

theorem comm_eq {x : Nat} (hx : x < 64) :
    n3Commutes (n3Arrs ()) (unpack 1782 11 (N3T x)) = zc (N3T x) := by
  have cx : Cn (N3T x) := CFSG.KS.Raw.Orb.allN_iff.1 c3T x hx
  unfold n3Commutes zc
  rw [Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  have cg : Cn (N3G k) := (ok_spec (n3_facts hk).2).1
  rw [(n3_facts hk).1, comp_u cx cg, comp_u cg cx, beq_u (cpc cx cg) (cpc cg cx)]

theorem kz_parts : zIdx.length = 16 ∧ ∀ i ∈ zIdx, pc (N3T i) (N3T i) = e := by
  have h : (Nat.beq zIdx.length 16 && zIdx.all fun i => Nat.beq (pc (N3T i) (N3T i)) e) = true :=
    kOne0
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun i hi => Nat.eq_of_beq_eq_true (h.2 i hi)⟩

theorem wordOK_all : (rWordOK () && (g2WordOK () && (g3WordOK () && (qWordOK () &&
    (cWordOK () && wWordOK ()))))) = true := by
  decide +kernel

end CertificateChecks.KernelSpor.S1379101

end
