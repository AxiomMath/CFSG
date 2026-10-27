module

public import Certificates.Kernel.SporSch.Tits.Common
public import Certificates.Kernel.SporSch.Tits.GenOrder
public import Certificates.Kernel.Sporadic.Tits.Texts2268
public import CFSG.Certificates.Kernel.SporSch.TitsLinesSound
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
meta import CFSG.Sporadic.Schreier.TitsActionCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSporSch.TitsLF 14 CFSG.Sporadic.Schreier.Tits.titsLineFlagArr
#kst_order CertificateChecks.KernelSporSch.TitsLK 12 2925 CFSG.Sporadic.Schreier.Tits.titsLineKey

namespace CertificateChecks.KernelSporSch.TitsAction

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon

@[expose] noncomputable def lpK (i : Nat) : Nat :=
  pg 12 (mask 12) (TMaps.F 0) (pg 14 (mask 14) TitsLF i)

@[expose] noncomputable def posK (v x : Nat) : Nat :=
  nIf(Nat.beq (lpK (3 * v)) x, 0, nIf(Nat.beq (lpK (3 * v + 1)) x, 1,
    nIf(Nat.beq (lpK (3 * v + 2)) x, 2, 3)))

@[expose] noncomputable def keyK (v : Nat) : Nat :=
  (lpK (3 * v) * 1755 + lpK (3 * v + 1)) * 1755 + lpK (3 * v + 2)

theorem hB : Nat.beq (Nat.shiftRight (TMaps.F 0) (8775 * 12)) 0 = true := by quickRfl
theorem hK : Nat.beq (Nat.shiftRight (TMaps.F 1) (8775 * 12)) 0 = true := by quickRfl
theorem hLF : Nat.beq (Nat.shiftRight TitsLF (8775 * 14)) 0 = true := by quickRfl
theorem hF : allN 4 (fun i => Nat.beq (Nat.shiftRight (T8775.F i) (8775 * 14)) 0) = true := by
  quickRfl
theorem hA : allN 4 (fun i => Nat.beq (Nat.shiftRight (T2925.F i) (2925 * 12)) 0) = true := by
  quickRfl
theorem hG : allN 4 (fun i => Nat.beq (Nat.shiftRight (TitsText.F i) (1755 * 11)) 0) = true := by
  quickRfl

theorem kLF : lineFlagsK 8775 2925 12 (TMaps.F 1) 12 (TMaps.F 0) 14 TitsLF = true := by quickRfl

theorem k1 : allN 4 (fun i => allN 8775 (fun j =>
    Nat.beq (pg 12 (mask 12) (TMaps.F 0) (pg 14 (mask 14) (T8775.F i) j))
      (pg 11 (mask 11) (TitsText.F i) (pg 12 (mask 12) (TMaps.F 0) j)))) = true := by quickRfl

theorem k2 : allN 4 (fun i => allN 8775 (fun j =>
    Nat.beq (pg 12 (mask 12) (TMaps.F 1) (pg 14 (mask 14) (T8775.F i) j))
      (pg 12 (mask 12) (T2925.F i) (pg 12 (mask 12) (TMaps.F 1) j)))) = true := by quickRfl

theorem k3 : allN 2925 (fun v => allN 3 (fun k =>
    bAnd(Nat.blt (pg 14 (mask 14) TitsLF (3 * v + k)) 8775,
      Nat.beq (pg 12 (mask 12) (TMaps.F 1) (pg 14 (mask 14) TitsLF (3 * v + k))) v))) = true := by
  quickRfl

theorem k4 : allN 2925 (fun v => bAnd(Nat.blt (lpK (3 * v)) (lpK (3 * v + 1)),
    bAnd(Nat.blt (lpK (3 * v + 1)) (lpK (3 * v + 2)), Nat.blt (lpK (3 * v + 2)) 1755))) = true := by
  quickRfl

theorem k5 : allN 8775 (fun j => bAnd(Nat.blt (pg 12 (mask 12) (TMaps.F 1) j) 2925,
    bAnd(Nat.blt (posK (pg 12 (mask 12) (TMaps.F 1) j) (pg 12 (mask 12) (TMaps.F 0) j)) 3,
      Nat.beq (pg 14 (mask 14) TitsLF (3 * pg 12 (mask 12) (TMaps.F 1) j +
        posK (pg 12 (mask 12) (TMaps.F 1) j) (pg 12 (mask 12) (TMaps.F 0) j))) j))) = true := by
  quickRfl

theorem k6 : orderK 2925 keyK TitsLK.SO TitsLK.SOI 12 = true := by quickRfl

theorem lt_of {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.blt_eq ▸ h

theorem lf_eq : titsLineFlagArr = unpack 8775 14 TitsLF := by
  have e : titsLineFlagArr = lineFlags 8775 2925 titsKappaArr titsBetaArr := rfl
  rw [e, kappa_eq, beta_eq]
  exact lineFlagsK_sound kLF

theorem map_get {A : Array Nat} {f : Nat → Nat} {i : Nat} (hi : i < A.size) :
    (A.map f)[i]! = f A[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos A i hi]

theorem beta_get (x : Nat) : titsBetaArr[x]! = pg 12 (mask 12) (TMaps.F 0) x := by
  rw [beta_eq, unpack_get0 hB]

theorem kappa_get (x : Nat) : titsKappaArr[x]! = pg 12 (mask 12) (TMaps.F 1) x := by
  rw [kappa_eq, unpack_get0 hK]

theorem lf_get (x : Nat) : titsLineFlagArr[x]! = pg 14 (mask 14) TitsLF x := by
  rw [lf_eq, unpack_get0 hLF]

theorem lp_get {i : Nat} (hi : i < 8775) : titsLinePtArr[i]! = lpK i := by
  rw [titsLinePtArr, map_get (by rw [lf_eq]; simpa [unpack] using hi), lf_get, beta_get]
  rfl

theorem flag_get {i : Nat} (hi : i < 4) (x : Nat) :
    (titsFlagArrs[i]!)[x]! = pg 14 (mask 14) (T8775.F i) x := by
  rw [titsFlagArrs, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    arr8775_eq (by omega), unpack_get0 (allN_spec hF i hi)]

theorem star_get {i : Nat} (hi : i < 4) (x : Nat) :
    (titsAStarArrs[i]!)[x]! = pg 12 (mask 12) (T2925.F i) x := by
  rw [titsAStarArrs, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    arr2925_eq (by omega), unpack_get0 (allN_spec hA i hi)]

theorem gen_get {i : Nat} (hi : i < 4) (x : Nat) :
    (titsGenArrs[i]!)[x]! = pg 11 (mask 11) (TitsText.F i) x := by
  rw [gen_eq hi, unpack_get0 (allN_spec hG i hi)]

theorem pos_eq {v x : Nat} (hv : v < 2925) : titsLinePos v x = posK v x := by
  unfold titsLinePos posK
  rw [lp_get (by omega), lp_get (by omega), lp_get (by omega)]
  cases h0 : Nat.beq (lpK (3 * v)) x
  · rw [if_neg (Nat.ne_of_beq_eq_false h0)]
    cases h1 : Nat.beq (lpK (3 * v + 1)) x
    · rw [if_neg (Nat.ne_of_beq_eq_false h1)]
      cases h2 : Nat.beq (lpK (3 * v + 2)) x
      · rw [if_neg (Nat.ne_of_beq_eq_false h2)]
      · rw [if_pos (Nat.eq_of_beq_eq_true h2)]
    · rw [if_pos (Nat.eq_of_beq_eq_true h1)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h0)]

theorem key_eq {v : Nat} (hv : v < 2925) : titsLineKey v = keyK v := by
  unfold titsLineKey keyK
  rw [lp_get (by omega), lp_get (by omega), lp_get (by omega)]

theorem facts : (∀ i < 4, ∀ j < 8775, titsBetaArr[(titsFlagArrs[i]!)[j]!]! =
      (titsGenArrs[i]!)[titsBetaArr[j]!]!) ∧
    (∀ i < 4, ∀ j < 8775, titsKappaArr[(titsFlagArrs[i]!)[j]!]! =
      (titsAStarArrs[i]!)[titsKappaArr[j]!]!) ∧
    (∀ v < 2925, ∀ k < 3, titsLineFlagArr[3 * v + k]! < 8775 ∧
      titsKappaArr[titsLineFlagArr[3 * v + k]!]! = v ∧
      titsBetaArr[titsLineFlagArr[3 * v + k]!]! = titsLinePtArr[3 * v + k]!) ∧
    (∀ v < 2925, titsLinePtArr[3 * v]! < titsLinePtArr[3 * v + 1]! ∧
      titsLinePtArr[3 * v + 1]! < titsLinePtArr[3 * v + 2]! ∧ titsLinePtArr[3 * v + 2]! < 1755) ∧
    (∀ j < 8775, titsLinePos titsKappaArr[j]! titsBetaArr[j]! < 3 ∧
      titsLineFlagArr[3 * titsKappaArr[j]! + titsLinePos titsKappaArr[j]! titsBetaArr[j]!]! = j) ∧
    (((List.range 2925).map titsLineKey).mergeSort fun a b => decide (a ≤ b)).Pairwise
      (· < ·) := by
  refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_, fun v hv k hk => ?_, fun v hv => ?_,
    fun j hj => ?_, ?_⟩
  · rw [flag_get hi, gen_get hi, beta_get, beta_get]
    exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec k1 i hi) j hj)
  · rw [flag_get hi, star_get hi, kappa_get, kappa_get]
    exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec k2 i hi) j hj)
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec k3 v hv) k hk)
    have hlt : 3 * v + k < 8775 := by omega
    rw [lf_get, kappa_get, beta_get, lp_get hlt]
    exact ⟨lt_of h1, Nat.eq_of_beq_eq_true h2, rfl⟩
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec k4 v hv)
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    rw [lp_get (by omega), lp_get (by omega), lp_get (by omega)]
    exact ⟨lt_of h1, lt_of h2, lt_of h3⟩
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec k5 j hj)
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    rw [kappa_get, beta_get, pos_eq (lt_of h1), lf_get]
    exact ⟨lt_of h2, Nat.eq_of_beq_eq_true h3⟩
  · have e : (List.range 2925).map titsLineKey = (List.range 2925).map keyK :=
      List.map_congr_left fun v hv => key_eq (List.mem_range.1 hv)
    rw [e]
    exact orderK_sound k6

end CertificateChecks.KernelSporSch.TitsAction

end
