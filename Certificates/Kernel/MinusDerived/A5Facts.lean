module

public import Certificates.Kernel.MinusDerived.A5Checks
public import Certificates.Kernel.MinusDerived.Facts2
public import Certificates.Kernel.MinusEnum.TableFacts
public import CFSG.Certificates.Kernel.Misc.PermWitSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelMinusA5

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
  CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CertificateChecks.KernelMinusL

local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem numsF : SF.ng = 2 ∧ SF.N = 60 := by
  have h := kNumsF
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem bindF : minusA5Gens.size = 2 ∧ ∀ k < 2, minusA5Gens[k]! = unpack 65 7 (SF.G k) :=
  binds_of_check kBindF

theorem permF : ∀ k < SF.ng,
    permOK 65 7 (mask 7) (65 * 7) (SF.G k) (pinvS 65 7 (mask 7) (SF.G k)) = true := by
  intro k hk
  rw [numsF.1] at hk
  exact AI.1 kPermF k hk

theorem keyInjF {N : ℕ} {T : ℕ → ℕ} {SK : List ℕ} (hK : keysSK 65 7 minusBase N T SK = true) :
    ∀ i < N, ∀ j < N, keyA 65 minusBase (unpack 65 7 (T i)) =
      keyA 65 minusBase (unpack 65 7 (T j)) → i = j := by
  intro i hi j hj e
  rw [keyA_unpack KernelMinusEnum.keysM, keyA_unpack KernelMinusEnum.keysM] at e
  exact keysSK_spec hK i hi j hj e

theorem pinF : (minusA5Enum ()).pts = Array.ofFn (n := SF.N) fun i => unpack 65 7 (SF.T i.val) :=
  enumBfs_pts_base (by rw [bindF.1, numsF.1])
    (fun k hk => bindF.2 k (by rw [numsF.1] at hk; exact hk)) SF.ok KernelMinusEnum.keysM kKF
    (by have := numsF.2; omega)

theorem enumF : enumOK 65 minusA5Gens minusBase (minusA5Enum ()) = true :=
  enumOK_of_bfsK_base (by rw [bindF.1, numsF.1])
    (fun k hk => bindF.2 k (by rw [numsF.1] at hk; exact hk)) permF SF.ok KernelMinusEnum.keysM
    kKF (by have := numsF.2; omega)

theorem enumOKF : minusA5EnumOK () = true := by
  have hs : (minusA5Enum ()).pts.size = 60 := by rw [pinF, Array.size_ofFn, numsF.2]
  simp only [minusA5EnumOK, Bool.and_eq_true, beq_iff_eq]
  exact ⟨enumF, hs⟩

theorem simpleF : minusA5Simple () = true := by
  have hN := numsF.2
  unfold minusA5Simple
  refine conjSimpleOK_of_ctree (WT := WF) KernelMinusEnum.kSz KernelMinusEnum.keysM enumF pinF
    (fun i hi => AI.1 kPermTF i (by rw [hN] at hi; exact hi))
    (Nat.eq_of_beq_eq_true kT0F) (keyInjF kKF) (fun k hk => ?_)
  rw [hN] at hk ⊢
  have h := AI.1 kTreeF k hk
  rw [Bool.or_eq_true] at h
  exact h.imp id fun h' => AI.1 h'

theorem c0 : canonK 65 7 (mask 7) (65 * 7) (LX 0) = true := canX (by norm_num)
theorem c1 : canonK 65 7 (mask 7) (65 * 7) (LX 1) = true := canX (by norm_num)
theorem c00 : canonK 65 7 (mask 7) (65 * 7) (pcomp 65 7 (mask 7) (LX 0) (LX 0)) = true :=
  canonK_pcomp c0 c0

theorem validL : minusLocalValid () = true := by
  unfold minusLocalValid
  rw [← loc0, ← loc1, ← loc2, ← loc3, validX (by norm_num), validX (by norm_num),
    validX (by norm_num), validX (by norm_num), KernelMinusEnum.rowM (by norm_num),
    validA_unpack (KernelMinusEnum.permM (by norm_num))]
  rfl

theorem ordA : minusSylowAOrder () = true := by
  unfold minusSylowAOrder
  rw [← loc0, bindX.2 0 (by norm_num), compA_unpack c0 c0, compA_unpack c00 c00,
    idA_eq KernelMinusEnum.kSz, eqA_unpack (canonK_pcomp c00 c00) canI, eqA_unpack c00 canI]
  simpa [pa, ia] using kOrdA

theorem sqB : minusSylowBSq () = true := by
  unfold minusSylowBSq
  rw [← loc1, bindX.2 1 (by norm_num), compA_unpack c1 c1, idA_eq KernelMinusEnum.kSz,
    eqA_unpack (canonK_pcomp c1 c1) canI]
  exact kSqB

theorem conjB : minusSylowConj () = true := by
  unfold minusSylowConj
  rw [← loc0, ← loc1, bindX.2 0 (by norm_num), bindX.2 1 (by norm_num), compA_unpack c1 c0,
    compA_unpack (canonK_pcomp c1 c0) c1, compA_unpack c0 c0, compA_unpack c00 c0,
    eqA_unpack (canonK_pcomp (canonK_pcomp c1 c0) c1) (canonK_pcomp c00 c0)]
  exact kConjB

theorem notMemB : minusSylowNotMem () = true := by
  unfold minusSylowNotMem
  rw [← loc0, ← loc1, bindX.2 0 (by norm_num), bindX.2 1 (by norm_num),
    idA_eq KernelMinusEnum.kSz, compA_unpack c0 c0, compA_unpack c00 c0, eqA_unpack c1 canI,
    eqA_unpack c1 c0, eqA_unpack c1 c00, eqA_unpack c1 (canonK_pcomp c00 c0)]
  simpa [pa, ia] using kNotMem

theorem genX {k : ℕ} (hk : k < 2) : minusA5Gens[k]! = unpack 65 7 (LX (k + 2)) := by
  interval_cases k
  · rw [← loc2, bindX.2 2 (by norm_num)]
  · rw [← loc3, bindX.2 3 (by norm_num)]

theorem commF : minusA5Commute () = true := by
  unfold minusA5Commute
  rw [allLt_iff]
  intro k hk
  rw [bindF.1] at hk
  have hc := canX (k := k + 2) (by omega)
  have hg := KernelMinusEnum.gCM (k := 0) (by norm_num)
  rw [genX hk, KernelMinusEnum.rowM (by norm_num), compA_unpack hc hg, compA_unpack hg hc,
    eqA_unpack (canonK_pcomp hc hg) (canonK_pcomp hg hc)]
  exact AI.1 kComm k hk

theorem localCheck : minusLocalCheck () = true := by
  simp only [minusLocalCheck, validL, ordA, sqB, conjB, notMemB, commF, enumOKF, simpleF,
    Bool.and_self]

end CertificateChecks.KernelMinusA5

end
