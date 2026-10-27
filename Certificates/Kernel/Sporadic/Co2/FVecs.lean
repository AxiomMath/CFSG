
module

public import CFSG.Sporadic.Co2Cert.FaithfulBase
public import CFSG.Certificates.Kernel.Spor.DistinctSound
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.SpanningLinearAction
public import CFSG.Sporadic.Co2Cert.FaithfulCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2Faith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open CFSG.Monster.B.Co2.Native CFSG.KS CFSG.KS.Co2Shape CFSG.KC.Enum

@[expose] def PL : List Nat := co2Rec.vectors.map packVec

theorem packed_eq : co2PackedVecs = PL.toArray := by
  unfold co2PackedVecs PL
  rfl

theorem size_ok : co2PackedVecs.size = 2300 := by
  decide +kernel

theorem bounds_ok : PL.all (fun x => decide (x < 2 ^ 22) && x != 0) = true := by
  decide +kernel

theorem buckets_ok : allN 64 (fun b => distinctL (2 ^ 16) (bucketL 16 b PL) 0) = true := by
  quickRfl

theorem packed_facts : ∀ i < 2300, co2PackedVecs[i]! < 2 ^ 22 ∧ co2PackedVecs[i]! ≠ 0 ∧
    ∀ j < 2300, co2PackedVecs[i]! = co2PackedVecs[j]! → i = j := by
  have hlen : PL.length = 2300 := by
    have := size_ok
    rwa [packed_eq, List.size_toArray] at this
  have get : ∀ k (hk : k < 2300), co2PackedVecs[k]! = PL[k]'(by rw [hlen]; exact hk) :=
    fun k hk => by
    rw [packed_eq, getElem!_pos _ k (by simp [hlen]; exact hk), List.getElem_toArray]
  have hbd : ∀ x ∈ PL, x < 2 ^ 22 ∧ x ≠ 0 := fun x hx => by
    have hb := List.all_eq_true.1 bounds_ok x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
    exact hb
  have hnd : PL.Nodup := nodup_of_bucketsK (k := 16) (n := 64)
    (fun x hx => (hbd x hx).1) (fun b hb => allN_spec buckets_ok b hb)
  intro i hi
  have hb := hbd _ (List.getElem_mem (l := PL) (n := i) (by rw [hlen]; exact hi))
  refine ⟨by rw [get i hi]; exact hb.1, by rw [get i hi]; exact hb.2, fun j hj e => ?_⟩
  rw [get i hi, get j hj] at e
  exact (List.Nodup.getElem_inj_iff hnd).1 e

end CertificateChecks.KernelSpor.Co2Faith

end
