module

public import Certificates.Kernel.Item434Gen.HeChecksA
public import Certificates.Kernel.Item434Gen.HeChecks0
public import Certificates.Kernel.Item434Gen.HeChecks1
public import Certificates.Kernel.Item434Gen.HeChecks2
public import Certificates.Kernel.Item434Gen.HeChecks3
public import CFSG.Certificates.Kernel.Item434GenSound
public import Certificates.Kernel.LocalComp.HeFixBind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelItem434.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
open CFSG.KC.Item434Gen CFSG.Sporadic.HeldB CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem kBind : (Nat.beq (CertificateChecks.KernelLC.HeFix.HG.F 0) (HV 0) &&
    Nat.beq (CertificateChecks.KernelLC.HeFix.HG.F 1) (HV 2)) = true := by quickRfl

theorem kSz : szOK 8330 14 = true := by quickRfl

theorem gen_eq : heGen 0 = unpack 8330 14 (HV 0) ∧ heGen 1 = unpack 8330 14 (HV 2) := by
  have h := kBind
  rw [Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · rw [CertificateChecks.KernelLC.HeFix.heGen_eq (k := 0) (by decide), Nat.eq_of_beq_eq_true h.1]
  · rw [CertificateChecks.KernelLC.HeFix.heGen_eq (k := 1) (by decide), Nat.eq_of_beq_eq_true h.2]

theorem heCheck_true : heCheck = true := by
  have hw := kSz
  obtain ⟨xp, xi⟩ := (by simpa only [Bool.and_eq_true] using kXI :
    permOK 8330 14 (mask 14) (8330 * 14) (HV 4) (HV 5) = true ∧
      permOK 8330 14 (mask 14) (8330 * 14) (HV 5) (HV 4) = true)
  obtain ⟨yp, yi⟩ := (by simpa only [Bool.and_eq_true] using kYI :
    permOK 8330 14 (mask 14) (8330 * 14) (HV 6) (HV 7) = true ∧
      permOK 8330 14 (mask 14) (8330 * 14) (HV 7) (HV 6) = true)
  obtain ⟨z1, z2⟩ := (by simpa only [Bool.and_eq_true] using kZ :
    Nat.beq (cmK 8330 14 (HV 4) (HV 5) (HV 6) (HV 7)) (HV 8) = true ∧
      heisK 8330 14 (HV 4) (HV 6) (HV 8) = true)
  obtain ⟨w1, w2⟩ := (by simpa only [Bool.and_eq_true] using kW :
    Nat.beq (pcK 8330 14 (HV 4) (HV 6)) (HV 9) = true ∧
      Nat.beq (pcK 8330 14 (HV 4) (pwK 8330 14 (HV 6) 2)) (HV 10) = true)
  have pX := pp_of_permOK hw xp
  have pY := pp_of_permOK hw yp
  obtain ⟨-, pZ, -⟩ := heis_eq hw xp xi yp yi (Nat.eq_of_beq_eq_true z1)
  have pW2 : PP 8330 14 (HV 9) := by
    rw [← Nat.eq_of_beq_eq_true w1]
    exact pX.mul pY
  have pW3 : PP 8330 14 (HV 10) := by
    rw [← Nat.eq_of_beq_eq_true w2]
    exact pX.mul (pp_ppow hw pY 2)
  have e0 := Eq.mp (Bool.and_eq_true _ _) k0e
  have e1 := Eq.mp (Bool.and_eq_true _ _) k1e
  have e2 := Eq.mp (Bool.and_eq_true _ _) k2e
  have e3 := Eq.mp (Bool.and_eq_true _ _) k3e
  have f0 := fix_sound hw (S := SV 0) (SI := SIV 0) (c := heFix0) (k := 4) kA kB rfl
    (fun j hj => match j, hj with
      | 0, _ => k0s0
      | 1, _ => k0s1
      | 2, _ => k0s2
      | 3, _ => k0s3) k0i k0a k0b pZ pX e0.1 e0.2
  have f1 := fix_sound hw (S := SV 1) (SI := SIV 1) (c := heFix1) (k := 4) kA kB rfl
    (fun j hj => match j, hj with
      | 0, _ => k1s0
      | 1, _ => k1s1
      | 2, _ => k1s2
      | 3, _ => k1s3) k1i k1a k1b pZ pY e1.1 e1.2
  have f2 := fix_sound hw (S := SV 2) (SI := SIV 2) (c := heFix2) (k := 4) kA kB rfl
    (fun j hj => match j, hj with
      | 0, _ => k2s0
      | 1, _ => k2s1
      | 2, _ => k2s2
      | 3, _ => k2s3) k2i k2a k2b pZ pW2 e2.1 e2.2
  have f3 := fix_sound hw (S := SV 3) (SI := SIV 3) (c := heFix3) (k := 4) kA kB rfl
    (fun j hj => match j, hj with
      | 0, _ => k3s0
      | 1, _ => k3s1
      | 2, _ => k3s2
      | 3, _ => k3s3) k3i k3a k3b pZ pW3 e3.1 e3.2
  unfold heCheck
  rw [gen_eq.1, gen_eq.2]
  exact ex27_sound hw kA kB kX kY xp xi yp yi z1 z2 w1 w2 f0 f1 f2 f3

end CertificateChecks.KernelItem434.He

end
