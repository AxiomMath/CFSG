module

public import Certificates.Kernel.Sporadic.OddCore.SuzRKF
public import Certificates.Kernel.Sporadic.OddCore.SuzRKZ

public section

namespace CertificateChecks.KernelSpor.SuzRKZF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.RootTwistCheck
open CFSG.Sporadic.SuzRecog.RootTwistData CFSG.Sporadic.SuzRecog.ModelGroupsCheck
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzRKF CertificateChecks.KernelSpor.SuzRKZ

theorem rho_eq : CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr = unpack 1782 11 (SuzRKR.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzRKR.all 0 (by norm_num)
  rw [← SuzRKR.eq, Nat.mul_zero] at h
  exact h

theorem b00 : Nat.beq 0 0 = true := rfl
theorem b10 : Nat.beq 1 0 = false := rfl
theorem b11 : Nat.beq 1 1 = true := rfl
theorem b20 : Nat.beq 2 0 = false := rfl
theorem b21 : Nat.beq 2 1 = false := rfl
theorem b22 : Nat.beq 2 2 = true := rfl
theorem b30 : Nat.beq 3 0 = false := rfl
theorem b31 : Nat.beq 3 1 = false := rfl
theorem b32 : Nat.beq 3 2 = false := rfl

theorem bIf_t {t e : Bool} : Bool.rec (motive := fun _ => Bool) e t true = t := rfl

theorem bIf_f {t e : Bool} : Bool.rec (motive := fun _ => Bool) e t false = e := rfl

theorem eqA_false {t u : Array Nat} {x : Nat} (hx : x < 1782) (h : t[x]! ≠ u[x]!) :
    eqA 1782 t u = false := by
  rw [Bool.eq_false_iff]
  intro he
  have := (CFSG.Monster.B.Co2.allLt_iff.1 he) x hx
  rw [beq_iff_eq] at this
  exact h this

theorem canT {i : Nat} (hi : i < 3456) : canonK 1782 11 (mask 11) (1782 * 11) (SuzRKT i) = true :=
  rec.2.2.2.2.2.1 i hi

theorem canG {s : Nat} (hs : s < 4) : canonK 1782 11 (mask 11) (1782 * 11) (SuzRKG s) = true :=
  rec.2.2.2.2.2.2 s hs

theorem comm_false {i s x : Nat} (hi : i < 3456) (hs : s < 4) (hx : x < 1782)
    (h : movK (SuzRKT i) (SuzRKG s) x = true) :
    commA kEls[i]! (unpack 1782 11 (SuzRKG s)) = false := by
  unfold commA
  refine eqA_false hx ?_
  rw [kEls_get hi, CFSG.Monster.B.Co2.compA_get hx, CFSG.Monster.B.Co2.compA_get hx,
    unpack_get hx, unpack_get hx, unpack_get (canon_lt (canG hs) hx),
    unpack_get (canon_lt (canT hi) hx)]
  unfold movK at h
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem kCentreOK_true : kCentreOK = true := by
  unfold kCentreOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  have h := allN_spec zAll i hi
  unfold zK at h
  simp only [strictB_eq, bAnd_iff] at h
  obtain ⟨hx, h⟩ := h
  generalize SuzRKW i = w at h hx
  have e1 : Nat.mod w 4 = w % 4 := rfl
  have e2 : Nat.div w 4 = w / 4 := rfl
  rw [e1, e2] at h
  rw [e2] at hx
  have hx := blt_true hx
  have hc : w % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hA : kGenAArr = unpack 1782 11 (SuzRKG 0) := kGenA_eq
  have hB : kGenBArr = unpack 1782 11 (SuzRKG 1) := kGenB_eq
  rcases (by omega : w % 4 = 0 ∨ w % 4 = 1 ∨ w % 4 = 2 ∨ w % 4 = 3) with c | c | c | c
  · simp only [c, b00] at h
    have := comm_false hi (by norm_num) hx h
    rw [← hA] at this
    simp [this]
  · simp only [c, b10, b11] at h
    have := comm_false hi (by norm_num) hx h
    rw [← hB] at this
    simp [this]
  · simp only [c, b20, b21, b22] at h
    have hp : eqA 1782 (CFSG.Sporadic.SuzOddCore.powA 1782 kEls[i]! 3) (idA 1782) = false := by
      refine eqA_false hx ?_
      have ht : ∀ y < 1782, pg 11 (mask 11) (SuzRKT i) y < 1782 := fun y hy => canon_lt (canT hi) hy
      simp only [CFSG.Sporadic.SuzOddCore.powA]
      rw [CFSG.Monster.B.Co2.compA_get hx, CFSG.Monster.B.Co2.compA_get hx,
        CFSG.Monster.B.Co2.compA_get hx, CFSG.Monster.B.Co2.idA_get hx, kEls_get hi,
        unpack_get hx, unpack_get (ht _ hx), unpack_get (ht _ (ht _ hx))]
      intro e
      simp only [e, Nat.beq_refl] at h
      exact Bool.false_ne_true h
    simp [hp]
  · simp only [c, b30, b31, b32] at h
    rw [kEls_get hi]
    by_cases h0 : w / 4 = 0
    · simp only [h0, b00] at h
      rw [Nat.eq_of_beq_eq_true h, ← idA_eq, eqA_self]
      simp
    · have hz : Nat.beq (w / 4) 0 = false :=
        Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
      simp only [hz] at h
      by_cases h1 : w / 4 = 1
      · simp only [h1, b11] at h
        rw [Nat.eq_of_beq_eq_true h, ← rho_eq, eqA_self]
        simp
      · have hz1 : Nat.beq (w / 4) 1 = false :=
          Bool.eq_false_iff.2 fun e => h1 (Nat.eq_of_beq_eq_true e)
        simp only [hz1] at h
        rw [Nat.eq_of_beq_eq_true h, ← CFSG.KC.BfsPin.compA_unpack canR canR, ← rho_eq, eqA_self]
        simp

end CertificateChecks.KernelSpor.SuzRKZF

end
