module

public import Certificates.Kernel.SporSch.J4S.FormK
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
import CFSG.Certificates.Kernel.SporSch.J4SFormTr
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.J4Form

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4Real

theorem up_get {i : Nat} (hi : i < 112) : formUpRows[i]?.getD 0 =
    ((formRows[i]?.getD 0) >>> (i + 1) <<< (i + 1)) ||| 2 ^ i := by
  simp [formUpRows, hi]

theorem rowJ_lt (P r : Nat) : rowJ rm P r < 2 ^ 112 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem hR : WfN formRows ∧ encN formRows = J4FR := pack_enc fr

theorem hI : WfN formInvRows ∧ encN formInvRows = J4FI := pack_enc fi

theorem hU : WfN formUpRows ∧ encN formUpRows = J4FU := by
  unfold formUpRows
  refine ofFn_enc hK (fun i => ?_) fuc (fun i => Nat.eq_of_beq_eq_true (allN_spec fu i i.isLt))
  have e : rowJ rm J4FU i.val =
      ((formRows[i.val]?.getD 0) >>> (i.val + 1) <<< (i.val + 1)) ||| 2 ^ i.val :=
    Nat.eq_of_beq_eq_true (allN_spec fu i i.isLt)
  rw [← e]
  exact rowJ_lt _ _

theorem defect_eq {G : Array Nat} {P : Nat} (hG : WfN G) (hP : encN G = P) :
    defectOK G = defK P := by
  have m1 := mulRows_enc hK hG hU.1
  have tG := tr_enc_proved hK hG
  have m2 := mulRows_enc hK m1.1 tG.1
  have xD := xor_enc m2.1 hU.1
  have lD := lower_enc xD.1
  have tL := tr_enc_proved hK lD.1
  have xL := xor_enc lD.1 tL.1
  simp only [defectOK, formDefect]
  rw [beq_enc xD.1 xL.1, xL.2, tL.2, lD.2, xD.2, m2.2, m1.2, tG.2, hP, hU.2, defK,
    CFSG.KC.J4Q.strictB_eq]

theorem facts : (xorRows112 formUpRows (transposeRows 112 formUpRows) = formRows ∧
      (∀ i < 112, ∀ j < 112, (formUpRows[i]?.getD 0).testBit j =
        if i < j then (formRows[i]?.getD 0).testBit j else decide (i = j)) ∧
      (∀ i < 112, formUpRows[i]?.getD 0 < 2 ^ 112) ∧ formRows.size = 112 ∧
      (∀ i < 112, formRows[i]?.getD 0 < 2 ^ 112))
    ∧ (mulRows 112 formRows formInvRows = idRows 112 ∧ mulRows 112 formInvRows formRows = idRows 112)
    ∧ (defectOK An.1 = true ∧ defectOK Bn.1 = true) := by
  have tU := tr_enc_proved hK hU.1
  have xU := xor_enc hU.1 tU.1
  have m1 := mulRows_enc hK hR.1 hI.1
  have m2 := mulRows_enc hK hI.1 hR.1
  refine ⟨⟨?_, fun i hi j hj => ?_, fun i hi => ?_, hR.1.1, fun i hi => ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · apply enc_inj xU.1 hR.1
    rw [xU.2, tU.2, hU.2, hR.2]
    exact Nat.eq_of_beq_eq_true sym
  · rw [up_get hi, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Nat.testBit_two_pow]
    by_cases h : i < j
    · rw [ite_eq_left h, show i + 1 + (j - (i + 1)) = j by omega]
      simp [show i + 1 ≤ j by omega, show i ≠ j by omega]
    · rw [ite_eq_right h]
      simp [show ¬ (i + 1 ≤ j) by omega]
  · have e : rowJ rm J4FU i = ((formRows[i]?.getD 0) >>> (i + 1) <<< (i + 1)) ||| 2 ^ i :=
      Nat.eq_of_beq_eq_true (allN_spec fu i hi)
    rw [up_get hi, ← e]
    exact rowJ_lt _ _
  · rw [Array.getElem?_eq_getElem (by rw [hR.1.1]; exact hi), Option.getD_some,
      ← getElem!_pos formRows i (by rw [hR.1.1]; exact hi)]
    exact hR.1.2 i hi
  · apply enc_inj m1.1 (CFSG.KS.SporSch.J4B.id_enc hK).1
    rw [m1.2, hR.2, hI.2, (CFSG.KS.SporSch.J4B.id_enc hK).2]
    exact Nat.eq_of_beq_eq_true inv1
  · apply enc_inj m2.1 (CFSG.KS.SporSch.J4B.id_enc hK).1
    rw [m2.2, hR.2, hI.2, (CFSG.KS.SporSch.J4B.id_enc hK).2]
    exact Nat.eq_of_beq_eq_true inv2
  · rw [defect_eq hA.1 hA.2]
    exact defA
  · rw [defect_eq hB.1 hB.2]
    exact defB

end CertificateChecks.KernelSporSch.J4Form

end
