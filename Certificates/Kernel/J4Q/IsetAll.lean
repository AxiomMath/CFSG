module

public import Certificates.Kernel.J4Q.IsetA
public import Certificates.Kernel.J4Q.IsetB
public import Certificates.Kernel.J4Q.IsetCkA
public import Certificates.Kernel.J4Q.IsetCkB

public section

namespace CertificateChecks.KernelJ4Q

theorem ic_half {f : Nat → Bool} {h : Nat} (hf : ∀ c, f c = icH h c) (hall : ∀ c < 338, f c = true)
    {c : Nat} (h1 : 338 * h ≤ c) (h2 : c < 338 * h + 338) : icK c = true := by
  have k := hall (c - 338 * h) (by omega)
  rw [hf] at k
  unfold icH at k
  have e : Nat.add (Nat.mul 338 h) (c - 338 * h) = c := by
    change 338 * h + (c - 338 * h) = c
    omega
  rw [e] at k
  exact k

theorem ic_spec {c : Nat} (hc : c < 676) : icK c = true := by
  by_cases h1 : c < 338
  · exact ic_half (h := 0) (fun _ => rfl) CFSG.KD.J4Q.ICA.all (by omega) (by omega)
  · exact ic_half (h := 1) (fun _ => rfl) CFSG.KD.J4Q.ICB.all (by omega) (by omega)

theorem iC_half {f : Nat → Bool} {h : Nat} (hf : ∀ c, f c = iCH h c) (hall : ∀ c < 338, f c = true)
    {c : Nat} (h1 : 338 * h ≤ c) (h2 : c < 338 * h + 338) : iCK c = true := by
  have k := hall (c - 338 * h) (by omega)
  rw [hf] at k
  unfold iCH at k
  have e : Nat.add (Nat.mul 338 h) (c - 338 * h) = c := by
    change 338 * h + (c - 338 * h) = c
    omega
  rw [e] at k
  exact k

theorem iC_spec {c : Nat} (hc : c < 676) : iCK c = true := by
  by_cases h1 : c < 338
  · exact iC_half (h := 0) (fun _ => rfl) CFSG.KD.J4Q.IKA.all (by omega) (by omega)
  · exact iC_half (h := 1) (fun _ => rfl) CFSG.KD.J4Q.IKB.all (by omega) (by omega)

end CertificateChecks.KernelJ4Q

end
