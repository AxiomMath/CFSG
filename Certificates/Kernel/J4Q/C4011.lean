module

public import Certificates.Kernel.J4Q.VlOk
import Certificates.Kernel.J4Q.VlJ0
import Certificates.Kernel.J4Q.VlJ1
import Certificates.Kernel.J4Q.VlE
import Certificates.Kernel.J4Q.VlS0
import Certificates.Kernel.J4Q.VlS1
import Certificates.Kernel.J4Q.VlS2
import Certificates.Kernel.J4Q.VlS3
import Certificates.Kernel.J4Q.VlP0
import Certificates.Kernel.J4Q.VlP1

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q

theorem seg_all : ∀ t < 256, segK t = true := by
  intro t ht
  by_cases h0 : t < 64
  · have h := CFSG.KD.J4Q.VSG0.all t h0
    unfold seg0 at h
    have e : Nat.add 0 t = t := Nat.zero_add t
    rwa [e] at h
  by_cases h1 : t < 128
  · have hb : t - 64 < 64 := by omega
    have h := CFSG.KD.J4Q.VSG1.all (t - 64) hb
    unfold seg1 at h
    have e : Nat.add 64 (t - 64) = t := by
      change 64 + (t - 64) = t
      omega
    rwa [e] at h
  by_cases h2 : t < 192
  · have hb : t - 128 < 64 := by omega
    have h := CFSG.KD.J4Q.VSG2.all (t - 128) hb
    unfold seg2 at h
    have e : Nat.add 128 (t - 128) = t := by
      change 128 + (t - 128) = t
      omega
    rwa [e] at h
  · have hb : t - 192 < 64 := by omega
    have h := CFSG.KD.J4Q.VSG3.all (t - 192) hb
    unfold seg3 at h
    have e : Nat.add 192 (t - 192) = t := by
      change 192 + (t - 192) = t
      omega
    rwa [e] at h

theorem vlj_all : ∀ j < 75, vlJK j = true := by
  intro j hj
  by_cases h0 : j < 38
  · exact CFSG.KD.J4Q.VLJ0.all j h0
  · have hb : j - 38 < 37 := by omega
    have h := CFSG.KD.J4Q.VLJ1.all (j - 38) hb
    unfold vlJ1 at h
    have e : Nat.add 38 (j - 38) = j := by
      change 38 + (j - 38) = j
      omega
    rwa [e] at h

theorem pair_all : ∀ p < 1980, pairAtK p = true := by
  intro p hp
  have hq : ∀ q < 198, pairK q = true := by
    intro q hq
    by_cases h0 : q < 99
    · have h := CFSG.KD.J4Q.VPA0.all q h0
      unfold pair0 pairH at h
      have e : Nat.add (Nat.mul 99 0) q = q := by
        change 99 * 0 + q = q
        omega
      rwa [e] at h
    · have hb : q - 99 < 99 := by omega
      have h := CFSG.KD.J4Q.VPA1.all (q - 99) hb
      unfold pair1 pairH at h
      have e : Nat.add (Nat.mul 99 1) (q - 99) = q := by
        change 99 * 1 + (q - 99) = q
        omega
      rwa [e] at h
  have h := allR_spec (hq (p / 10) (by omega)) (p % 10) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 10 (p / 10)) (p % 10) = p := by
    change 10 * (p / 10) + p % 10 = p
    omega
  beta_reduce at h
  rwa [e] at h

theorem c4011 : CFSG.Sporadic.J4.QT2.chkVlAll = true :=
  vlAll_of vlj_all CFSG.KD.J4Q.ETCA.all seg_all pair_all

end CertificateChecks.KernelJ4Q

end
