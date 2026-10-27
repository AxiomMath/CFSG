module

public import Certificates.Kernel.MinusDerived.Checks
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedCheck
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace CertificateChecks.KernelMinusL

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
  CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem nums : PL.ng = 5 ∧ PL.N = 7800 := by
  have h := kNums
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem bind : minusLGens.size = 5 ∧ ∀ k < 5, minusLGens[k]! = unpack 65 7 (PL.G k) :=
  binds_of_check kBind

theorem perm : ∀ k < PL.ng,
    permOK 65 7 (mask 7) (65 * 7) (PL.G k) (pinvS 65 7 (mask 7) (PL.G k)) = true := by
  intro k hk
  rw [nums.1] at hk
  exact AI.1 kPerm k hk

theorem keysOKm : ∀ p ∈ minusBase, p < 65 := by decide

theorem pinL : (minusLEnum ()).pts = Array.ofFn (n := PL.N) fun i => unpack 65 7 (PL.T i.val) :=
  enumBfs_pts_base (by rw [bind.1, nums.1])
    (fun k hk => bind.2 k (by rw [nums.1] at hk; exact hk)) PL.ok keysOKm kK
    (by rw [nums.2])

theorem enum_ok : minusLEnumCheck (minusLEnum ()) = true := by
  have he : enumOK 65 minusLGens minusBase (minusLEnum ()) = true :=
    enumOK_of_bfsK_base (by rw [bind.1, nums.1])
      (fun k hk => bind.2 k (by rw [nums.1] at hk; exact hk)) perm PL.ok keysOKm kK
      (by rw [nums.2])
  unfold minusLEnumCheck
  rw [he, pinL, Array.size_ofFn, nums.2]
  rfl

theorem size_ok : minusLSizeCheck (minusLEnum ()) = true := by
  unfold minusLSizeCheck
  rw [allLt_iff]
  intro i hi
  rw [pinL, Array.size_ofFn] at hi
  rw [pinL, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
  simp [unpack]

end CertificateChecks.KernelMinusL
