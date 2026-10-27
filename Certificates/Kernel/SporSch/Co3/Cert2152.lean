
module

public import Certificates.Kernel.SporSch.Co3.Bind12
public import Certificates.Kernel.Sporadic.Co3.Bind
public import Certificates.Kernel.Sporadic.Co3.Bind36
public import CFSG.Certificates.Kernel.SporSch.DerivsSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co3Cert

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem perm276 : allN 111 (fun j => permOK 276 9 (mask 9) (276 * 9) (Co3Text.L j)
    (pinvS 276 9 (mask 9) (Co3Text.L j))) = true := by quickRfl

theorem perm36 : allN 83 (fun j => permOK 36 6 (mask 6) (36 * 6) (Co3Text36.L j)
    (pinvS 36 6 (mask 6) (Co3Text36.L j))) = true := by quickRfl

theorem perm12 : allN 14 (fun j => permOK 12 4 (mask 4) (12 * 4) (Co3Text12.L j)
    (pinvS 12 4 (mask 4) (Co3Text12.L j))) = true := by quickRfl

theorem d1 : derivK 2 14 co3ChainDerivations = true := by quickRfl
theorem d2 : derivK 2 14 co3CoprimeDerivations = true := by quickRfl
theorem d3 : derivK 8 10 co3TDerivations = true := by quickRfl
theorem d4 : derivK 7 14 co3MDerivations = true := by quickRfl
theorem d5 : derivK 6 11 co3M1Derivations = true := by quickRfl
theorem d6 : derivK 4 8 co3MCommDerivations = true := by quickRfl
theorem d7 : derivK 3 8 co3M1CommDerivations = true := by quickRfl
theorem d8 : derivK 13 25 co3JointDerivations = true := by quickRfl
theorem d9 : derivK 63 66 co3Sp36Derivations = true := by quickRfl
theorem d10 : derivK 6 16 co3M36Derivations = true := by quickRfl
theorem d11 : derivK 5 13 co3M112Derivations = true := by quickRfl

theorem isInv_of {n w P : Nat} {a : Array Nat} (ha : a = unpack n w P)
    (h : permOK n w (mask w) (n * w) P (pinvS n w (mask w) P) = true) :
    isInvA n a (invCand n a) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound (r := pinvS n w (mask w) P) h
  rw [ha, h1]
  exact h2

theorem layout :
    layoutOK co3Bytes276 3 276 111 = true ∧ layoutOK co3Bytes36 2 36 83 = true ∧
    layoutOK co3Bytes12 1 12 14 = true ∧ layoutOK co3FormsBytes 1 64 276 = true ∧
    (∀ L < 111, isInvA 276 (co3Arr276 L) (invCand 276 (co3Arr276 L)) = true) ∧
    (∀ L < 83, isInvA 36 (co3Arr36 L) (invCand 36 (co3Arr36 L)) = true) ∧
    (∀ L < 14, isInvA 12 (co3Arr12 L) (invCand 12 (co3Arr12 L)) = true) ∧
    (∀ r < 276, co3FormWord r < 2 ^ 253) := by
  refine ⟨?_, ?_, ?_, ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_,
    fun r hr => Co3Forms.word_lt hr⟩
  · rw [co3Bytes276, Co3Text.eq]
    exact hexBind_layout Co3Text.all rfl
  · rw [co3Bytes36, Co3Text36.eq]
    exact hexBind_layout Co3Text36.all rfl
  · rw [co3Bytes12, Co3Text12.eq]
    exact hexBind_layout Co3Text12.all rfl
  · rw [co3FormsBytes, Co3Forms.eq]
    exact hexBind_layout Co3Forms.all rfl
  · have h := CFSG.KS.Text.hexBind_sound Co3Text.all L hL
    rw [Nat.zero_add, ← Co3Text.eq] at h
    exact isInv_of h (allN_spec perm276 L hL)
  · have h := CFSG.KS.Text.hexBind_sound Co3Text36.all L hL
    rw [Nat.zero_add, ← Co3Text36.eq] at h
    exact isInv_of h (allN_spec perm36 L hL)
  · have h := CFSG.KS.Text.hexBind_sound Co3Text12.all L hL
    rw [Nat.zero_add, ← Co3Text12.eq] at h
    exact isInv_of h (allN_spec perm12 L hL)

theorem words :
    wordsOK 2 14 co3ChainDerivations = true ∧ wordsOK 2 14 co3CoprimeDerivations = true ∧
    wordsOK 8 10 co3TDerivations = true ∧ wordsOK 7 14 co3MDerivations = true ∧
    wordsOK 6 11 co3M1Derivations = true ∧ wordsOK 4 8 co3MCommDerivations = true ∧
    wordsOK 3 8 co3M1CommDerivations = true ∧ wordsOK 13 25 co3JointDerivations = true ∧
    wordsOK 63 66 co3Sp36Derivations = true ∧ wordsOK 6 16 co3M36Derivations = true ∧
    wordsOK 5 13 co3M112Derivations = true :=
  ⟨derivK_sound d1, derivK_sound d2, derivK_sound d3, derivK_sound d4, derivK_sound d5,
    derivK_sound d6, derivK_sound d7, derivK_sound d8, derivK_sound d9, derivK_sound d10,
    derivK_sound d11⟩

end CertificateChecks.KernelSporSch.Co3Cert

end
