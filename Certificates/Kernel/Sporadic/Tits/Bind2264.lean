module

public import Certificates.Kernel.Sporadic.Tits.ChainD
public import Certificates.Kernel.Sporadic.Tits.ChainAP
public import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelMisc

theorem field_get {L₀ m j : Nat} (hj : j < m) (hL : L₀ + m ≤ 96) :
    (titsField1755 L₀ m)[j]! = unpack 1755 11 (TitsText.F (L₀ + j)) := by
  rw [titsField1755, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    TitsText.titsArr1755_eq (by omega)]

theorem sOKA : allN 14 (fun j => Nat.beq (TitsA.S j) (TitsText.F (Nat.add 4 j))) = true := by
  quickRfl
theorem sOKD : allN 13 (fun j => Nat.beq (TitsD.S j) (TitsText.F (Nat.add 18 j))) = true := by
  quickRfl
theorem sOKP : allN 12 (fun j => Nat.beq (TitsP.S j) (TitsText.F (Nat.add 31 j))) = true := by
  quickRfl

theorem baseA : allN 6 (fun t => Nat.beq (baseArr 1755 titsAmbientBase)[t]! (pg 11 (mask 11) TitsA.BP t)) =
    true := by quickRfl
theorem baseD : allN 6 (fun t => Nat.beq (baseArr 1755 titsDerivedBase)[t]! (pg 11 (mask 11) TitsD.BP t)) =
    true := by quickRfl
theorem baseP : allN 7 (fun t => Nat.beq (baseArr 1755 titsPerfectBase)[t]! (pg 11 (mask 11) TitsP.BP t)) =
    true := by quickRfl

theorem permA : allN 14 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsA.S j) (TitsA.SI j)) =
    true := by quickRfl
theorem permD : allN 13 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsD.S j) (TitsD.SI j)) =
    true := by quickRfl
theorem permP : allN 12 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsP.S j) (TitsP.SI j)) =
    true := by quickRfl
theorem permG : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsText.F j)
    (pinvS 1755 11 (mask 11) (TitsText.F j))) = true := by quickRfl

theorem sAll : (∀ j < 14, TitsA.S j = TitsText.F (4 + j)) ∧ (∀ j < 13, TitsD.S j = TitsText.F (18 + j)) ∧
    (∀ j < 12, TitsP.S j = TitsText.F (31 + j)) :=
  ⟨fun j hj => Nat.eq_of_beq_eq_true (allN_spec sOKA j hj),
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec sOKD j hj),
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec sOKP j hj)⟩

theorem bAll : (∀ t < 6, (baseArr 1755 titsAmbientBase)[t]! = pg 11 (mask 11) TitsA.BP t) ∧
    (∀ t < 6, (baseArr 1755 titsDerivedBase)[t]! = pg 11 (mask 11) TitsD.BP t) ∧
    (∀ t < 7, (baseArr 1755 titsPerfectBase)[t]! = pg 11 (mask 11) TitsP.BP t) :=
  ⟨fun j hj => Nat.eq_of_beq_eq_true (allN_spec baseA j hj),
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec baseD j hj),
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec baseP j hj)⟩

theorem gen_eq {j : Nat} (hj : j < 4) : titsGenArrs[j]! = unpack 1755 11 (TitsText.F j) := by
  rw [titsGenArrs, field_get hj (by norm_num), Nat.zero_add]

theorem amb_eq {j : Nat} (hj : j < 14) : titsAmbientArrs[j]! = unpack 1755 11 (TitsA.S j) := by
  rw [titsAmbientArrs, field_get hj (by norm_num), sAll.1 j hj]

theorem der_eq {j : Nat} (hj : j < 13) : titsDerivedArrs[j]! = unpack 1755 11 (TitsD.S j) := by
  rw [titsDerivedArrs, field_get hj (by norm_num), sAll.2.1 j hj]

theorem perf_eq {j : Nat} (hj : j < 12) : titsPerfectArrs[j]! = unpack 1755 11 (TitsP.S j) := by
  rw [titsPerfectArrs, field_get hj (by norm_num), sAll.2.2 j hj]

theorem bindsA : Binds 1755 11 TitsA.S 14 6 TitsA.BP titsAmbientArrs (baseArr 1755 titsAmbientBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsAmbientArrs, titsField1755],
    fun j hj => amb_eq hj, by decide, bAll.1⟩

theorem bindsD : Binds 1755 11 TitsD.S 13 6 TitsD.BP titsDerivedArrs (baseArr 1755 titsDerivedBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsDerivedArrs, titsField1755],
    fun j hj => der_eq hj, by decide, bAll.2.1⟩

theorem bindsP : Binds 1755 11 TitsP.S 12 7 TitsP.BP titsPerfectArrs (baseArr 1755 titsPerfectBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [titsPerfectArrs, titsField1755],
    fun j hj => perf_eq hj, by decide, bAll.2.2⟩

end CertificateChecks.KernelSpor.Tits2264

end
