
module

public import CFSG.Sporadic.Co2Cert.FaithfulBase
public import Certificates.Kernel.Sporadic.Co2.Rels
public import CFSG.Certificates.Kernel.Spor.DistinctSound
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.SpanningLinearAction
public import CFSG.Sporadic.Co2Cert.FaithfulCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2Faith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open CFSG.Monster.B.Co2.Native CFSG.KS CFSG.KS.Co2Shape CFSG.KS.Ord

@[expose] def RA : Array Nat := #[2, 1, 8, 4, 64, 256, 16, 496, 32, 803, 1024, 2128, 4464, 65536,
  16467, 524288, 8192, 688208, 893008, 32768, 1122604, 2171171]

@[expose] def RB : Array Nat := #[4, 6, 16, 32, 128, 512, 1024, 149, 2048, 4096, 8192, 16384,
  32768, 131072, 262144, 8, 1048576, 177768, 318248, 2012152, 2097152, 1834943]

theorem mat_of_bits {R : Array Nat} {M : Nat} (hR : R.size = 22)
    (h : ∀ i < 22, ∀ j < 22,
      R[i]!.testBit j = (M / 2 ^ (132 * i + 6 * j) % 2 ^ 6 % 2 == 1)) :
    rowsMatrix 22 R = ordMat 2 22 6 132 M := by
  ext i j
  rw [rowsMatrix_apply, Array.getElem?_eq_getElem (by rw [hR]; exact i.2), Option.getD_some]
  unfold ordMat toVecD
  rw [natCast_zmod_two, ← h i i.2 j j.2, getElem!_pos R (i : ℕ) (by rw [hR]; exact i.2)]

theorem bitsA : ∀ i < 22, ∀ j < 22, RA[i]!.testBit j =
    (CFSG.KD.OrdCo2.RH 1 / 2 ^ (132 * i + 6 * j) % 2 ^ 6 % 2 == 1) := by
  decide +kernel

theorem bitsB : ∀ i < 22, ∀ j < 22, RB[i]!.testBit j =
    (CFSG.KD.OrdCo2.RH 2 / 2 ^ (132 * i + 6 * j) % 2 ^ 6 % 2 == 1) := by
  decide +kernel

theorem RA_mat : rowsMatrix 22 RA = ordMat 2 22 6 132 (CFSG.KD.OrdCo2.RH 1) :=
  mat_of_bits rfl bitsA

theorem RB_mat : rowsMatrix 22 RB = ordMat 2 22 6 132 (CFSG.KD.OrdCo2.RH 2) :=
  mat_of_bits rfl bitsB

theorem rows_eq_of_mat {R R' : Array Nat} (hR : R.size = 22) (hR' : R'.size = 22)
    (hl : ∀ i < 22, R[i]! < 2 ^ 22) (hl' : ∀ i < 22, R'[i]! < 2 ^ 22)
    (h : rowsMatrix 22 R = rowsMatrix 22 R') : R = R' := by
  apply Array.ext (hR.trans hR'.symm)
  intro i h1 h2
  have hi : i < 22 := hR ▸ h1
  have e := congrFun (congrFun h ⟨i, hi⟩)
  have e' : toVecD 22 (R[i]?.getD 0) = toVecD 22 (R'[i]?.getD 0) := funext fun j => e j
  rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at e'
  have b := hl i hi
  have b' := hl' i hi
  rw [getElem!_pos R i h1] at b
  rw [getElem!_pos R' i h2] at b'
  exact toVecD_injective b b' e'

theorem payload_facts (s : String) : (rowsOfPayload 22 s).size = 22 ∧
    ∀ i < 22, (rowsOfPayload 22 s)[i]! < 2 ^ 22 := by
  refine ⟨by unfold rowsOfPayload; simp, fun i hi => ?_⟩
  unfold rowsOfPayload
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact ofBits_lt 22 _

theorem rowsA_eq : co2RowsA = RA := by
  have hm : rowsMatrix 22 co2RowsA = rowsMatrix 22 RA := by
    rw [rowsMatrix_co2RowsA, RA_mat]
    have h := CertificateChecks.KernelSpor.Co2Rels.mA_eq
    change CFSG.Blueprint.NativeSporadic.decode 2 22 1 CFSG.Sporadic.Co2.Native.seedA = _ at h
    rw [co2SeedA_eq] at h
    exact h
  exact rows_eq_of_mat (payload_facts _).1 rfl (payload_facts _).2 (by decide) hm

theorem rowsB_eq : co2RowsB = RB := by
  have hm : rowsMatrix 22 co2RowsB = rowsMatrix 22 RB := by
    rw [rowsMatrix_co2RowsB, RB_mat]
    have h := CertificateChecks.KernelSpor.Co2Rels.mB_eq
    change CFSG.Blueprint.NativeSporadic.decode 2 22 1 CFSG.Sporadic.Co2.Native.seedB = _ at h
    rw [co2SeedB_eq] at h
    exact h
  exact rows_eq_of_mat (payload_facts _).1 rfl (payload_facts _).2 (by decide) hm

end CertificateChecks.KernelSpor.Co2Faith

end
