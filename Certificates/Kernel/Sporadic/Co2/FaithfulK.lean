
module

public import Certificates.Kernel.Sporadic.Co2.FVecs
public import Certificates.Kernel.Sporadic.Co2.FRows
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import CFSG.Certificates.Kernel.SporSch.PosTable
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2Faith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native

theorem basis_ok : co2BasisRows.size = 22 ∧ mulRows 22 co2BasisInv co2BasisRows = idRows 22 := by
  decide +kernel

theorem orders_ok : mulRows 22 RA RA = idRows 22 ∧ powRows 22 RB 5 = idRows 22 := by
  decide +kernel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
  CertificateChecks.KernelSporSch.Co2M in
theorem rowsA_ok : allN 22 (fun k => Nat.beq (pg 22 M22 (SR 0) k)
    ((transposeRows 22 RA)[k]?.getD 0)) = true := by
  quickRfl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
  CertificateChecks.KernelSporSch.Co2M in
theorem rowsB_ok : allN 22 (fun k => Nat.beq (pg 22 M22 (SR 1) k)
    ((transposeRows 22 RB)[k]?.getD 0)) = true := by
  quickRfl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
  CertificateChecks.KernelSporSch.Co2M in
theorem act_of_rows {s : ℕ} (hs : s < 2) {R : Array ℕ}
    (h : allN 22 (fun k => Nat.beq (pg 22 M22 (SR s) k) ((transposeRows 22 R)[k]?.getD 0)) = true) :
    ∀ i < 2300, vecMulN 22 (transposeRows 22 R) co2PackedVecs[i]! =
      co2PackedVecs[(co2OrigArrs[s]!)[i]!]! := by
  intro i hi
  have hr : Rep 22 co2PackedVecs (CFSG.Sporadic.Co2Schreier.aArrs[s]!) (SR s)
      (aT.getD s (0, 0)).2 := by
    have := repT_get aRep (k := s) (by simpa [aT] using hs)
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> exact this
  have hR : ∀ k < 22, row 22 (SR s) k = (transposeRows 22 R)[k]?.getD 0 := fun k hk => by
    rw [← Nat.eq_of_beq_eq_true (allN_spec h k hk)]
    exact (land_mask_eq_row M22_eq (SR s) k).symm
  rw [vecMulN_eq_vmul hR, ← (get_rep hr (by rw [V_size]; exact hi)).2]
  rfl

open CFSG.KC.Enum CFSG.KS.Co2M CertificateChecks.KernelSporSch.Co2M in
theorem bad_rowsA : Bool.not (allN 22 (fun k => Nat.beq (pg 22 M22 (Nat.xor (SR 0) 1) k)
    ((transposeRows 22 RA)[k]?.getD 0))) = true := by
  quickRfl

theorem actA : ∀ i < 2300, vecMulN 22 (transposeRows 22 RA) co2PackedVecs[i]! =
    co2PackedVecs[(co2OrigArrs[0]!)[i]!]! := act_of_rows (by decide) rowsA_ok

theorem actB : ∀ i < 2300, vecMulN 22 (transposeRows 22 RB) co2PackedVecs[i]! =
    co2PackedVecs[(co2OrigArrs[1]!)[i]!]! := act_of_rows (by decide) rowsB_ok

theorem facts : co2PackedVecs.size = 2300 ∧
      (∀ i < 2300, co2PackedVecs[i]! < 2 ^ 22 ∧ co2PackedVecs[i]! ≠ 0 ∧
        ∀ j < 2300, co2PackedVecs[i]! = co2PackedVecs[j]! → i = j) ∧
      co2BasisRows.size = 22 ∧ mulRows 22 co2BasisInv co2BasisRows = idRows 22 ∧
      (∀ i < 2300, vecMulN 22 (transposeRows 22 co2RowsA) co2PackedVecs[i]! =
        co2PackedVecs[(co2OrigArrs[0]!)[i]!]!) ∧
      (∀ i < 2300, vecMulN 22 (transposeRows 22 co2RowsB) co2PackedVecs[i]! =
        co2PackedVecs[(co2OrigArrs[1]!)[i]!]!) ∧
      mulRows 22 co2RowsA co2RowsA = idRows 22 ∧ powRows 22 co2RowsB 5 = idRows 22 := by
  rw [rowsA_eq, rowsB_eq]
  exact ⟨size_ok, packed_facts, basis_ok.1, basis_ok.2, actA, actB, orders_ok.1,
    orders_ok.2⟩

end CertificateChecks.KernelSpor.Co2Faith

end
