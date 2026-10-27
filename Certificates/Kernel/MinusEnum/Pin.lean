module

public import Certificates.Kernel.MinusEnum.Checks
public import CFSG.Certificates.Kernel.BfsPinKeySound
import CFSG.Certificates.Kernel.BfsPinUnpack

public section

namespace CertificateChecks.KernelMinusEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.OddTranspositions.PartThree

theorem nums : ME.ng = 65 ∧ ME.N = 15600 := by
  have h := kNums
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem bind : minusTable.size = ME.ng ∧ ∀ k < ME.ng, minusTable[k]! = unpack 65 7 (ME.G k) :=
  binds_of_check kBind

theorem canonT : ∀ i < ME.N, canonK 65 7 (mask 7) (65 * 7) (ME.T i) = true := ME.run.2

theorem minusEnum_pts :
    (minusEnum ()).pts = Array.ofFn (n := ME.N) fun i => unpack 65 7 (ME.T i.val) :=
  enumBfs_pts_key (SK := (List.range 15600).map ME.K) bind.1 bind.2 kSz (allN_spec kG) canonT
    (Nat.eq_of_beq_eq_true kT0) (by decide) kK ME.run.1 (by rw [nums.2])

end CertificateChecks.KernelMinusEnum

end
