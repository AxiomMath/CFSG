module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlF
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.B0Gluing CFSG.Sporadic.SuzRecog.B0GluingData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "T" => SuzC1ET.T
local notation "g6" => pg 6 (mask 6)

@[expose] noncomputable def pK (k y : Nat) : Nat :=
  nIf(bAnd(Nat.blt k 4, Nat.blt y 42), g6 (SuzGlR (Nat.succ k)) y, 0)

@[expose] noncomputable def zK (j x : Nat) : Nat :=
  nIf(bAnd(Nat.blt j 4, Nat.blt x 42), g6 (SuzGlR zIL[j]!) x, 0)

theorem kTG' : allN 4 (fun i => Nat.beq (T (Nat.succ i)) (SuzC1ET.G i)) = true := by quickRfl

theorem kCent : centRSearch pK zK = true := by quickRfl

theorem negCent : Bool.not (centRSearch pK (fun _ x => zK 0 x)) = true := by quickRfl

theorem rtabs_get {k : Nat} (hk : k < 64) : rtabs[k]! = resTab ttabs[k]! :=
  map_get _ (by rw [ttabs_size']; exact hk)

theorem p0_eq : (fun k y => (p0Gens[k]!)[y]!) = pK := by
  funext k y
  unfold pK
  by_cases hk : k < 4
  · have e : t0Tabs[k]! = ttabs[k + 1]! := by
      have e1 := (pT0 hk).1
      have e2 := (pTT (show k + 1 < 64 by omega)).1
      have e3 : T (k + 1) = SuzC1ET.G k := Nat.eq_of_beq_eq_true (allN_spec kTG' k hk)
      rw [e3] at e2
      exact e1.trans e2.symm
    have hp : p0Gens[k]! = unpack 42 6 (SuzGlR (k + 1)) := by
      rw [show p0Gens[k]! = resTab t0Tabs[k]! from ofFn_get' _ hk, e, ← rtabs_get (by omega),
        (qR (by omega)).1]
    rw [hp, blt_t hk]
    by_cases hy : y < 42
    · rw [unpack_getElem! hy, blt_t hy]
    · rw [getElem!_neg _ _ (by rw [CFSG.KS.PEnum.unpack_size]; exact hy), blt_f hy]
      rfl
  · rw [getElem!_neg p0Gens k (by simp [p0Gens]; omega), blt_f hk]
    rfl

theorem z_eq : (fun j x => (zRes[j]!)[x]!) = zK := by
  funext j x
  unfold zK
  by_cases hj : j < 4
  · have hz : zIL[j]! < 64 := by interval_cases j <;> decide
    have hp : zRes[j]! = unpack 42 6 (SuzGlR zIL[j]!) := by
      rw [show zRes[j]! = rtabs[zI[j]!]! from ofFn_get' _ hj, zI_eq, (qR hz).1]
    rw [hp, blt_t hj]
    by_cases hx : x < 42
    · rw [unpack_getElem! hx, blt_t hx]
    · rw [getElem!_neg _ _ (by rw [CFSG.KS.PEnum.unpack_size]; exact hx), blt_f hx]
      rfl
  · rw [getElem!_neg zRes j (by simp [zRes]; omega), blt_f hj]
    rfl

theorem centRCheck_true : centRCheck = true := by
  have h := kCent
  rw [← p0_eq, ← z_eq] at h
  exact h

end CertificateChecks.KernelSpor.SuzGl

end
