
module

public import Certificates.Kernel.LocalQT.He4148.Glue
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public import CFSG.Certificates.Kernel.HeFixKFix

public section

namespace CertificateChecks.KernelSporSch.HePt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB

theorem nget_get (l : List Nat) {i : Nat} (hi : i < l.length) : nget l i = l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (by simpa using hi)

theorem list_get {F : Array Nat} {D : List Nat} (hD : F.toList = D) {a : Nat} (ha : a < D.length) :
    F[a]! = nget D a := by
  have hs : a < F.size := by rw [← Array.length_toList, hD]; exact ha
  rw [getElem!_pos F a hs, nget_get D ha, ← Array.getElem_toList]
  simp only [hD]

theorem canon_lt {n w p a : Nat} (hp : canonK n w (mask w) (n * w) p = true) (ha : a < n) :
    pg w (mask w) p a < n := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  exact Eq.mp Nat.blt_eq (allN_spec hp.2.2 a ha)

theorem nget_lt {D : List Nat} {n k : Nat} (hlt : ∀ x ∈ D, x < n) (hk : k < D.length) :
    nget D k < n := by
  rw [nget_get D hk]
  exact hlt _ (List.getElem_mem _)

theorem inc_ok {F : Array Nat} {D : List Nat} (hD : F.toList = D) {n m : Nat} (hm : D.length = m)
    (hlt : ∀ x ∈ D, x < n) (hinc : ∀ k < m - 1, nget D k < nget D (k + 1)) :
    incListOK n m F = true := by
  unfold incListOK
  simp only [Bool.and_eq_true, beq_iff_eq, CertificateChecks.KernelSpor.OddCore.allLt_iff,
    decide_eq_true_eq]
  refine ⟨⟨by rw [← Array.length_toList, hD, hm], fun k hk => ?_⟩, fun k hk => ?_⟩
  · rw [list_get hD (by omega)]
    exact nget_lt hlt (by omega)
  · rw [list_get hD (by omega), list_get hD (by omega)]
    exact hinc k hk

theorem fixes_ok {F : Array Nat} {D : List Nat} (hD : F.toList = D) {n w m : Nat}
    (hm : D.length = m) {t : Array Nat} {P : Nat} (ht : t = unpack n w P) (hlt : ∀ x ∈ D, x < n)
    (h : allN m (fun k => Nat.beq (pg w (mask w) P (nget D k)) (nget D k)) = true) :
    fixesOK m t F = true := by
  unfold fixesOK
  rw [CertificateChecks.KernelSpor.OddCore.allLt_iff]
  intro k hk
  rw [list_get hD (by omega), ht, CFSG.KC.Misc.PairCount.unpack_get (nget_lt hlt (by omega)),
    Nat.eq_of_beq_eq_true (allN_spec h k hk)]
  exact beq_self_eq_true _

theorem agree_ok {F : Array Nat} {D : List Nat} (hD : F.toList = D) {n w m wσ : Nat}
    (hm : D.length = m) {g σ : Array Nat} {P Pσ : Nat} (hg : g = unpack n w P)
    (hσ : σ = unpack m wσ Pσ) (hσc : canonK m wσ (mask wσ) (m * wσ) Pσ = true)
    (hlt : ∀ x ∈ D, x < n)
    (h : allN m (fun k => Nat.beq (pg w (mask w) P (nget D k))
      (nget D (pg wσ (mask wσ) Pσ k))) = true) :
    agreeOK m g F σ = true := by
  unfold agreeOK
  rw [CertificateChecks.KernelSpor.OddCore.allLt_iff]
  intro k hk
  have hs := canon_lt hσc hk
  rw [list_get hD (by omega), hg, CFSG.KC.Misc.PairCount.unpack_get (nget_lt hlt (by omega)), hσ,
    CFSG.KC.Misc.PairCount.unpack_get hk, list_get hD (by omega),
    Nat.eq_of_beq_eq_true (allN_spec h k hk)]
  exact beq_self_eq_true _

theorem fixList_ok {F : Array Nat} {D : List Nat} (hD : F.toList = D) {n w m : Nat}
    (hm : D.length = m) {t : Array Nat} {P : Nat} (ht : t = unpack n w P) (hlt : ∀ x ∈ D, x < n)
    (hinc : ∀ k < m - 1, nget D k < nget D (k + 1))
    (h : allN m (fun k => Nat.beq (pg w (mask w) P (nget D k)) (nget D k)) = true)
    (hc : CFSG.KC.HeFixK.fixK n w P = m) :
    fixListOK n m t F = true := by
  unfold fixListOK
  simp only [Bool.and_eq_true, beq_iff_eq, CertificateChecks.KernelSpor.OddCore.allLt_iff,
    decide_eq_true_eq]
  refine ⟨⟨⟨by rw [← Array.length_toList, hD, hm], fun k hk => ⟨?_, ?_⟩⟩, fun k hk => ?_⟩, ?_⟩
  · rw [list_get hD (by omega)]
    exact nget_lt hlt (by omega)
  · rw [list_get hD (by omega), ht,
      CFSG.KC.Misc.PairCount.unpack_get (nget_lt hlt (by omega)),
      Nat.eq_of_beq_eq_true (allN_spec h k hk)]
  · rw [list_get hD (by omega), list_get hD (by omega)]
    exact hinc k hk
  · rw [ht, CFSG.KC.HeFixK.countP_fix, hc]

theorem perm_of {n w : Nat} {t : Array Nat} {P PI : Nat} (ht : t = unpack n w P)
    (h1 : invEqK n w (mask w) (n * w) P PI = true)
    (h2 : invEqK n w (mask w) (n * w) PI P = true) : permChk n t = true :=
  (CertificateChecks.KernelLQT.He4148.unpack_facts ht h1 h2).1

end CertificateChecks.KernelSporSch.HePt

end
