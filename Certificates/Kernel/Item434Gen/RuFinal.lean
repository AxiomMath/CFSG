module

public import Certificates.Kernel.Item434Gen.RuChecksA
public import Certificates.Kernel.Item434Gen.RuChecks0
public import Certificates.Kernel.Item434Gen.RuChecks1
public import Certificates.Kernel.Item434Gen.RuChecks2
public import Certificates.Kernel.Item434Gen.RuChecks3
public import CFSG.Certificates.Kernel.Item434GenSound
public import Certificates.Kernel.Misc.RuInv.Proof
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelItem434.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
open CFSG.KC.Item434Gen CFSG.Sporadic.RuSchreier CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem kBind : (Nat.beq CertificateChecks.KernelMisc.RuInv.AD.n0 (RV 0) &&
    Nat.beq CertificateChecks.KernelMisc.RuInv.AD.n1 (RV 2)) = true := by quickRfl

theorem kSz : szOK 4060 12 = true := by quickRfl

theorem gen_eq : ruArr4060 0 = unpack 4060 12 (RV 0) ∧ ruArr4060 1 = unpack 4060 12 (RV 2) := by
  have h := kBind
  rw [Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · rw [CertificateChecks.KernelMisc.RuInv.hA0, Nat.eq_of_beq_eq_true h.1]
  · rw [CertificateChecks.KernelMisc.RuInv.hA1, Nat.eq_of_beq_eq_true h.2]

theorem ruCheck_true : ruCheck = true := by
  have hw := kSz
  obtain ⟨xp, xi⟩ := (by simpa only [Bool.and_eq_true] using kXI :
    permOK 4060 12 (mask 12) (4060 * 12) (RV 4) (RV 5) = true ∧
      permOK 4060 12 (mask 12) (4060 * 12) (RV 5) (RV 4) = true)
  obtain ⟨yp, yi⟩ := (by simpa only [Bool.and_eq_true] using kYI :
    permOK 4060 12 (mask 12) (4060 * 12) (RV 6) (RV 7) = true ∧
      permOK 4060 12 (mask 12) (4060 * 12) (RV 7) (RV 6) = true)
  obtain ⟨z1, z2⟩ := (by simpa only [Bool.and_eq_true] using kZ :
    Nat.beq (cmK 4060 12 (RV 4) (RV 5) (RV 6) (RV 7)) (RV 8) = true ∧
      heisK 4060 12 (RV 4) (RV 6) (RV 8) = true)
  obtain ⟨w1, w2⟩ := (by simpa only [Bool.and_eq_true] using kW :
    Nat.beq (pcK 4060 12 (RV 4) (RV 6)) (RV 9) = true ∧
      Nat.beq (pcK 4060 12 (RV 4) (pwK 4060 12 (RV 6) 2)) (RV 10) = true)
  have pX := pp_of_permOK hw xp
  have pY := pp_of_permOK hw yp
  obtain ⟨-, pZ, -⟩ := heis_eq hw xp xi yp yi (Nat.eq_of_beq_eq_true z1)
  have pW2 : PP 4060 12 (RV 9) := by
    rw [← Nat.eq_of_beq_eq_true w1]
    exact pX.mul pY
  have pW3 : PP 4060 12 (RV 10) := by
    rw [← Nat.eq_of_beq_eq_true w2]
    exact pX.mul (pp_ppow hw pY 2)
  have e0 := Eq.mp (Bool.and_eq_true _ _) k0e
  have e1 := Eq.mp (Bool.and_eq_true _ _) k1e
  have e2 := Eq.mp (Bool.and_eq_true _ _) k2e
  have e3 := Eq.mp (Bool.and_eq_true _ _) k3e
  have f0 := fix_sound hw (S := SV 0) (SI := SIV 0) (c := ruFix0) (k := 4) kA kB rfl
    (fun j hj => match j, hj with
      | 0, _ => k0s0
      | 1, _ => k0s1
      | 2, _ => k0s2
      | 3, _ => k0s3) k0i k0a k0b pZ pX e0.1 e0.2
  have f1 := fix_sound hw (S := SV 1) (SI := SIV 1) (c := ruFix1) (k := 4) kA kB rfl
    (fun j hj => match j, hj with
      | 0, _ => k1s0
      | 1, _ => k1s1
      | 2, _ => k1s2
      | 3, _ => k1s3) k1i k1a k1b pZ pY e1.1 e1.2
  have f2 := fix_sound hw (S := SV 2) (SI := SIV 2) (c := ruFix2) (k := 4) kA kB rfl
    (fun j hj => match j, hj with
      | 0, _ => k2s0
      | 1, _ => k2s1
      | 2, _ => k2s2
      | 3, _ => k2s3) k2i k2a k2b pZ pW2 e2.1 e2.2
  have f3 := fix_sound hw (S := SV 3) (SI := SIV 3) (c := ruFix3) (k := 4) kA kB rfl
    (fun j hj => match j, hj with
      | 0, _ => k3s0
      | 1, _ => k3s1
      | 2, _ => k3s2
      | 3, _ => k3s3) k3i k3a k3b pZ pW3 e3.1 e3.2
  unfold ruCheck
  rw [gen_eq.1, gen_eq.2]
  exact ex27_sound hw kA kB kX kY xp xi yp yi z1 z2 w1 w2 f0 f1 f2 f3

end CertificateChecks.KernelItem434.Ru

end
