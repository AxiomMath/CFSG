module

public import Certificates.Kernel.J2Cover.G5110
public import Certificates.Kernel.J2Cover.M22Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J2ECheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J2ECheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelJ2Cover

open CFSG.ComponentClassification.J2Cover.Models CFSG.EvenSporadicStandard.Fin76b

@[expose] noncomputable def mF24592 (a b : Nat) : Nat :=
  Bool.rec (mulIdx a b) (Bool.rec (mulIdx a b) (mtK a b) (Nat.blt b 128)) (Nat.blt a 128)

theorem mF24592_eq : mulIdx = mF24592 := by
  funext a b
  unfold mF24592
  cases ha : Nat.blt a 128
  · rfl
  · cases hb : Nat.blt b 128
    · rfl
    · exact mulIdx_eq (Nat.blt_eq.mp ha) (Nat.blt_eq.mp hb)

@[expose] noncomputable def fix24592 (n a : Nat) : Bool :=
  decide (a < 128) && (!(mF24592 a a == 0 && a != 0) || fixP (ELT a) == n)

theorem kE24592 : TableE.eCheck 128 mF24592 4 = true := by quickRfl

theorem kFix24592 : (TableE.eList 128 mF24592 4).all (fix24592 11) = true := by quickRfl

open Certificates in
theorem c24592 : CFSG.EvenSporadicStandard.Fin76b.J2.j2ECheck = true := by
  unfold J2.j2ECheck
  rw [mF24592_eq, kE24592, Bool.true_and, List.all_eq_true]
  intro a ha
  have h := List.all_eq_true.1 kFix24592 a ha
  unfold fix24592 at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [eltArrs_eq a h.1, fixCount_unpack]
  exact h.2

end CertificateChecks.KernelJ2Cover

end
