module

public import Certificates.Kernel.EvenBN.K27016D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27016

open CertificateChecks.KernelEvenBN

theorem take_all_of_chunks {f : Nat → Bool} {L : List Nat} (n : Nat) : ∀ (k m : Nat),
    (∀ i < k, ((L.drop (m + n * i)).take n).all f = true) → ((L.drop m).take (n * k)).all f = true
  | 0, m, _ => by rw [Nat.mul_zero, List.take_zero]; rfl
  | k + 1, m, h => by
    have e1 : n * (k + 1) = n + n * k := by rw [Nat.mul_succ, Nat.add_comm]
    rw [e1, List.take_add, List.all_append, Bool.and_eq_true, List.drop_drop]
    refine ⟨by simpa using h 0 (by omega), take_all_of_chunks n k (m + n) fun i hi => ?_⟩
    have e : m + n + n * i = m + n * (i + 1) := by
      rw [Nat.mul_succ, Nat.add_assoc, Nat.add_comm n (n * i)]
    rw [e]
    exact h (i + 1) (by omega)

theorem e0 : ((CNtC.drop 0).take 4).all cKc = true := by quickRfl
theorem e4 : ((CNtC.drop 4).take 4).all cKc = true := by quickRfl
theorem e8 : ((CNtC.drop 8).take 4).all cKc = true := by quickRfl
theorem e12 : ((CNtC.drop 12).take 4).all cKc = true := by quickRfl
theorem e16 : ((CNtC.drop 16).take 4).all cKc = true := by quickRfl
theorem e20 : ((CNtC.drop 20).take 4).all cKc = true := by quickRfl
theorem e24 : ((CNtC.drop 24).take 4).all cKc = true := by quickRfl
theorem e28 : ((CNtC.drop 28).take 4).all cKc = true := by quickRfl
theorem e32 : ((CNtC.drop 32).take 4).all cKc = true := by quickRfl
theorem e36 : ((CNtC.drop 36).take 4).all cKc = true := by quickRfl
theorem e40 : ((CNtC.drop 40).take 4).all cKc = true := by quickRfl
theorem e44 : ((CNtC.drop 44).take 4).all cKc = true := by quickRfl
theorem e48 : ((CNtC.drop 48).take 4).all cKc = true := by quickRfl
theorem e52 : ((CNtC.drop 52).take 4).all cKc = true := by quickRfl
theorem e56 : ((CNtC.drop 56).take 4).all cKc = true := by quickRfl
theorem e60 : ((CNtC.drop 60).take 4).all cKc = true := by quickRfl
theorem e64 : ((CNtC.drop 64).take 4).all cKc = true := by quickRfl
theorem e68 : ((CNtC.drop 68).take 4).all cKc = true := by quickRfl
theorem e72 : ((CNtC.drop 72).take 4).all cKc = true := by quickRfl
theorem e76 : ((CNtC.drop 76).take 4).all cKc = true := by quickRfl
theorem e80 : ((CNtC.drop 80).take 4).all cKc = true := by quickRfl
theorem e84 : ((CNtC.drop 84).take 4).all cKc = true := by quickRfl
theorem e88 : ((CNtC.drop 88).take 4).all cKc = true := by quickRfl
theorem e92 : ((CNtC.drop 92).take 4).all cKc = true := by quickRfl
theorem e96 : ((CNtC.drop 96).take 4).all cKc = true := by quickRfl
theorem e100 : ((CNtC.drop 100).take 4).all cKc = true := by quickRfl
theorem e104 : ((CNtC.drop 104).take 4).all cKc = true := by quickRfl
theorem e108 : ((CNtC.drop 108).take 4).all cKc = true := by quickRfl
theorem e112 : ((CNtC.drop 112).take 4).all cKc = true := by quickRfl
theorem e116 : ((CNtC.drop 116).take 4).all cKc = true := by quickRfl
theorem e120 : ((CNtC.drop 120).take 4).all cKc = true := by quickRfl
theorem e124 : ((CNtC.drop 124).take 4).all cKc = true := by quickRfl

theorem k0 : ((CNtC.take 128).all cKc) = true := by
  have h := take_all_of_chunks (f := cKc) (L := CNtC) 4 32 0 fun i hi => by
    interval_cases i
    exacts [e0, e4, e8, e12, e16, e20, e24, e28, e32, e36, e40, e44, e48, e52, e56, e60, e64, e68,
      e72, e76, e80, e84, e88, e92, e96, e100, e104, e108, e112, e116, e120, e124]
  rwa [List.drop_zero] at h

end CertificateChecks.Batch27016

end
