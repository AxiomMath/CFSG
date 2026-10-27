module

public import Certificates.Kernel.S63K.HBind
public import CFSG.Certificates.Kernel.S63K.LowSound
public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.HD

open CFSG.D4Hex CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.KS.SporSch.M24

theorem beq_nat (a b : ℕ) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · exact beq_false_of_ne (Nat.ne_of_beq_eq_false h)
  · exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)

theorem permBytes_eq : permBytes = (String.ofList PC).toUTF8 := by
  unfold permBytes
  rw [PC_eq]

theorem lineBytes_eq : lineBytes = (String.ofList LC).toUTF8 := by
  unfold lineBytes
  rw [LC_eq]

theorem pa_get {j i : ℕ} (hj : j < 8) (hi : i < 819) :
    hexAtW permBytes (3 * (819 * j + i)) 3 = im j i ∧ im j i < 819 := by
  have h := MatL.allN_iff.1 (MatL.allN_iff.1 pa j hj) i hi
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  have hl := Nat.eq_of_beq_eq_true lenP
  rw [permBytes_eq, hexAtW_low lowP (by omega)]
  exact h

theorem perm_get {k x : ℕ} (hk : k < 8) (hx : x < 819) : (permArrs[k]!)[x]! = im k x := by
  have e1 : permArrs[k]! = permArr k := by
    rw [getElem!_pos permArrs k (by rw [permArrs_size]; exact hk)]
    simp [permArrs]
  rw [e1]
  unfold permArr
  rw [getElem!_pos _ x (by simp [hx]), Array.getElem_ofFn]
  exact (pa_get hk hx).1

theorem compA_get' {n : ℕ} {t u : Array ℕ} {i : ℕ} (hi : i < n) : (compA n t u)[i]! = t[u[i]!]! := by
  unfold compA
  rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]

theorem lt_get {i : ℕ} (hi : i < 7371) :
    lineTab[i]! = pg 12 (mask 12) LT i ∧ pg 12 (mask 12) LT i < 819 := by
  have h := MatL.allN_iff.1 lt i hi
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  have hl := Nat.eq_of_beq_eq_true lenL
  refine ⟨?_, h.2⟩
  unfold lineTab
  rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]
  change hexAtW lineBytes (3 * i) 3 = _
  rw [lineBytes_eq, hexAtW_low lowL (by omega)]
  exact h.1

end CertificateChecks.KernelS63.HD

end
