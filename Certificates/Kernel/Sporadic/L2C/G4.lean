
module

public import Certificates.Kernel.Sporadic.L2C.G3
public import Certificates.Kernel.Sporadic.L2.G5
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.L2CG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Sporadic.SuzRecog.LevelTwoCover
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.ElimCert
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K CertificateChecks.KernelSpor.L2CK
open CertificateChecks.KernelSpor.L2G (sB band bif_true nbeq nblt nble nblt_f nble_f allN_get
  nbr_get)

theorem cellVert'_eq {k : Nat} (hk : k < 4) : cellVert' k = v1K k := by
  have h := cellAll k hk
  unfold cellK at h
  rw [band, band, band, band] at h
  obtain ⟨-, -, -, c4, -⟩ := h
  exact L2G.actV_W (L2G.eltP (by omega)).1 (L2G.eltP (by omega)).2.1 (j := 0) (by norm_num) c4

attribute [local irreducible] nbr in
theorem posIn_eq {y k : Nat} (hk : k < 36) (h : posOK y k = true) : posIn 0 y = k := by
  unfold posOK at h
  rw [band, nbeq] at h
  obtain ⟨h1, h2⟩ := h
  unfold posIn
  have hs := L2G.nbr_size (x := 0) (by norm_num)
  have g : ∀ j (hj : j < (nbr[0]!).size), (nbr[0]!)[j] = nbK 0 j := fun j hj => by
    have hj' : j < 36 := by
      rw [hs] at hj
      exact hj
    rw [← getElem!_pos _ j hj, nbr_get (by norm_num) hj']
  have hk' : k < (nbr[0]!).size := by
    rw [hs]
    exact hk
  rw [Array.findIdx?_eq_some_iff_getElem.2 ⟨hk', by rw [g, h1]; exact beq_self_eq_true y,
    fun j hj => by
      rw [g, beq_iff_eq]
      have := allN_get h2 hj
      rw [not_true] at this
      exact nbeq_f this⟩]
  rfl

theorem listed_of {y k : Nat} (hk : k < 36) (h : posOK y k = true) : listedAt0 y = true := by
  unfold listedAt0
  rw [posIn_eq hk h, nbr_get (by norm_num) hk]
  unfold posOK at h
  rw [band, nbeq] at h
  simp [hk, h.1]

theorem liftAt0_of {y k : Nat} (hk : k < 36) (h : posOK y k = true) : liftAt0 y = nbC 0 k := by
  unfold liftAt0
  rw [posIn_eq hk h, nbrC_low (by norm_num) (by norm_num) hk]

theorem lift2 (HB : BaseH) {y k : Nat} (hk : k < 36) (h : posOK y k = true) (hy : 2835 ≤ y) :
    nbC 0 k < 8991 ∧ 2835 ≤ nbC 0 k % 2997 ∧ nbC 0 k ≠ 342 := by
  have e : nbK 0 k = y := by
    unfold posOK at h
    rw [band, nbeq] at h
    exact h.1
  have h1 := nbC_lt HB (u := 0) (by norm_num) hk
  have h2 := nbC_mod HB (u := 0) (by norm_num) hk
  rw [Nat.zero_mod, e] at h2
  refine ⟨h1, by omega, fun e' => ?_⟩
  rw [e'] at h2
  omega

theorem adj_pos (HB : BaseH) {y k j : Nat} (hk : k < 36) (h : posOK y k = true) (hy : 2835 ≤ y)
    (hj : j < 36) (e : nbC 342 j = nbC 0 k) : adjB nbrC 342 (nbC 0 k) = true :=
  adjB_listed (by norm_num) (by norm_num) hj e (lift2 HB hk h hy).2.2.symm

theorem adj_neg (HB : BaseH) {y k : Nat} (hk : k < 36) (h : posOK y k = true) (hy : 2835 ≤ y)
    (hn : allN 36 (fun j => Bool.not (Nat.beq (nbC 342 j) (nbC 0 k))) = true) :
    adjB nbrC 342 (nbC 0 k) = false := by
  obtain ⟨h1, h2, -⟩ := lift2 HB hk h hy
  rw [adjB_nbrC (by norm_num) h1]
  unfold adjC occC
  rw [show Nat.blt (Nat.mod 342 2997) 2835 = true from rfl, nblt_f (b := 2835) (by
    change ¬ nbC 0 k % 2997 < 2835
    omega)]
  have : anyN 36 (fun j => Nat.beq (nbC 342 j) (nbC 0 k)) = false := by
    cases ha : anyN 36 (fun j => Nat.beq (nbC 342 j) (nbC 0 k))
    · rfl
    · obtain ⟨j, hj, e⟩ := anyN_iff.1 ha
      have := allN_get hn hj
      rw [e] at this
      exact absurd this (by decide)
  rw [this]
  cases Bool.not (Nat.beq 342 (nbC 0 k)) <;> rfl

theorem coverLocOK_true (HB : BaseH) (h : L2CK.locK = true) : coverLocOK = true := by
  unfold L2CK.locK at h
  simp only [band] at h
  obtain ⟨q0, q18, q19, q23, q27, q28, q33, q34, e0, a0, a2, n1, n3, b0, b2⟩ := h
  rw [nbeq] at e0 a0 a2 b0 b2
  have hp1c : p1c = 342 := by
    unfold p1c
    rw [L2G.p1_eq, liftAt0_of (by norm_num) q0, e0]
  have c0 : cellc 0 = nbC 0 19 := by
    unfold cellc
    exact liftAt0_of (by norm_num) q19
  have c1 : cellc 1 = nbC 0 23 := by
    unfold cellc
    exact liftAt0_of (by norm_num) q23
  have c2 : cellc 2 = nbC 0 27 := by
    unfold cellc
    exact liftAt0_of (by norm_num) q27
  have c3 : cellc 3 = nbC 0 34 := by
    unfold cellc
    exact liftAt0_of (by norm_num) q34
  have d0 : cellc' 0 = nbC 0 33 := by
    unfold cellc'
    rw [cellVert'_eq (by norm_num)]
    exact liftAt0_of (by norm_num) q33
  have d2 : cellc' 2 = nbC 0 28 := by
    unfold cellc'
    rw [cellVert'_eq (by norm_num)]
    exact liftAt0_of (by norm_num) q28
  have L : allLt 4 (fun k => listedAt0 cellReps[k]! && listedAt0 (cellVert' k)) = true := by
    rw [allLt_iff]
    intro k hk
    rw [cellVert'_eq hk, Bool.and_eq_true]
    interval_cases k
    · exact ⟨listed_of (by norm_num) q19, listed_of (by norm_num) q33⟩
    · exact ⟨listed_of (by norm_num) q23, listed_of (by norm_num) q34⟩
    · exact ⟨listed_of (by norm_num) q27, listed_of (by norm_num) q28⟩
    · exact ⟨listed_of (by norm_num) q34, listed_of (by norm_num) q23⟩
  unfold coverLocOK
  rw [L2G.p1_eq, listed_of (by norm_num) q0, listed_of (by norm_num) q18, L, hp1c, c0, c1, c2, c3,
    d0, d2, adj_pos HB (by norm_num) q19 (by norm_num) (by norm_num) a0,
    adj_pos HB (by norm_num) q27 (by norm_num) (by norm_num) a2,
    adj_neg HB (by norm_num) q23 (by norm_num) n1, adj_neg HB (by norm_num) q34 (by norm_num) n3,
    adj_pos HB (by norm_num) q33 (by norm_num) (by norm_num) b0,
    adj_pos HB (by norm_num) q28 (by norm_num) (by norm_num) b2]
  rfl

end CertificateChecks.KernelSpor.L2CG

end
