module

public import Certificates.Kernel.MinusDerived.Checks2
public import Certificates.Kernel.MinusDerived.Facts
public import Certificates.Kernel.MinusEnum.Pin
public import CFSG.Certificates.Kernel.PermPinKSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelMinusL

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KC.BfsPin CFSG.KC.PermPinK CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CertificateChecks.KernelMinusEnum
local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem canL {j : ℕ} (hj : j < 7800) : canonK 65 7 (mask 7) (65 * 7) (PL.T j) = true :=
  AI.1 kCanL j hj

theorem canG {k : ℕ} (hk : k < 5) : canonK 65 7 (mask 7) (65 * 7) (PL.G k) = true :=
  AI.1 (Bool.and_eq_true _ _ ▸ kCanG).1 k hk

theorem canX {k : ℕ} (hk : k < 4) : canonK 65 7 (mask 7) (65 * 7) (LX k) = true :=
  AI.1 (Bool.and_eq_true _ _ ▸ kCanG).2 k hk

theorem canE {i : ℕ} (hi : i < 15600) : canonK 65 7 (mask 7) (65 * 7) (ME.T i) = true :=
  KernelMinusEnum.canonT i (by rw [KernelMinusEnum.nums.2]; exact hi)

theorem canME {i : ℕ} (hi : i < 65) : canonK 65 7 (mask 7) (65 * 7) (ME.G i) = true :=
  AI.1 KernelMinusEnum.kG i (by rw [KernelMinusEnum.nums.1]; exact hi)

theorem rowE {i : ℕ} (hi : i < 65) : minusTable[i]! = unpack 65 7 (ME.G i) :=
  KernelMinusEnum.bind.2 i (by rw [KernelMinusEnum.nums.1]; exact hi)

theorem ptL {j : ℕ} (hj : j < PL.N) : (minusLEnum ()).pts[j]! = unpack 65 7 (PL.T j) := by
  rw [pinL, getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj), Array.getElem_ofFn]

theorem ptE {j : ℕ} (hj : j < ME.N) : (minusEnum ()).pts[j]! = unpack 65 7 (ME.T j) := by
  rw [KernelMinusEnum.minusEnum_pts, getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj),
    Array.getElem_ofFn]

theorem refl_ok : minusLReflCheck (minusLEnum ()) = true := by
  unfold minusLReflCheck
  rw [allLt_iff]
  intro j hj
  rw [pinL, Array.size_ofFn] at hj
  rw [allLt_iff]
  intro i hi
  rw [ptL hj, rowE hi, eqA_unpack (canL (by rw [nums.2] at hj; exact hj)) (canME hi)]
  exact AI.1 (AI.1 kRefl j (by rw [nums.2] at hj; exact hj)) i hi

theorem jOf_lt {k : ℕ} : jOf k < 65 := by
  unfold jOf
  cases Nat.beq k 0 <;> cases Nat.beq k 1 <;> cases Nat.beq k 2 <;> cases Nat.beq k 3 <;> decide

theorem gen_eq {k : ℕ} (hk : k < 5) :
    eqA 65 minusLGens[k]! (compA 65 minusTable[0]! minusTable[jOf k]!) = true := by
  rw [bind.2 k hk, rowE (by norm_num), rowE jOf_lt, compA_unpack (canME (by norm_num)) (canME jOf_lt),
    eqA_unpack (canG hk) (canonK_pcomp (canME (by norm_num)) (canME jOf_lt))]
  exact AI.1 kGensP k hk

theorem gens_ok : minusLGensCheck () = true := by
  unfold minusLGensCheck
  have hv : allLt 5 (fun k => validA 65 minusLGens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    rw [bind.2 k hk]
    exact validA_unpack (perm k (by rw [nums.1]; exact hk))
  have g0 : eqA 65 minusLGens[0]! (compA 65 minusTable[0]! minusTable[1]!) = true :=
    gen_eq (k := 0) (by norm_num)
  have g1 : eqA 65 minusLGens[1]! (compA 65 minusTable[0]! minusTable[3]!) = true :=
    gen_eq (k := 1) (by norm_num)
  have g2 : eqA 65 minusLGens[2]! (compA 65 minusTable[0]! minusTable[4]!) = true :=
    gen_eq (k := 2) (by norm_num)
  have g3 : eqA 65 minusLGens[3]! (compA 65 minusTable[0]! minusTable[10]!) = true :=
    gen_eq (k := 3) (by norm_num)
  have g4 : eqA 65 minusLGens[4]! (compA 65 minusTable[0]! minusTable[11]!) = true :=
    gen_eq (k := 4) (by norm_num)
  rw [bind.1, hv, g0, g1, g2, g3, g4]
  rfl

theorem canI : canonK 65 7 (mask 7) (65 * 7) (pidn 65 7) = true := by
  rw [← Nat.eq_of_beq_eq_true KernelMinusEnum.kT0]
  exact canE (by norm_num)

theorem cent_pt {i : ℕ} (hi : i < 15600) : centPt i = true := by
  have h5 : i / 3900 < 4 := by omega
  have h1 : 3900 * (i / 3900) ≤ i := Nat.mul_div_le i 3900
  have h2 : i < 3900 * (i / 3900) + 3900 := by omega
  interval_cases hq : i / 3900
  · exact AI.1 ch1383008c_0 i (by omega)
  · have := AI.1 ch1383008c_1 (i - 3900) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  · have := AI.1 ch1383008c_2 (i - 7800) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  · have := AI.1 ch1383008c_3 (i - 11700) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this

theorem cent_ok : minusLCentralCheck (minusEnum ()) = true := by
  unfold minusLCentralCheck
  rw [allLt_iff]
  intro i hi
  rw [KernelMinusEnum.minusEnum_pts, Array.size_ofFn, KernelMinusEnum.nums.2] at hi
  have hN : i < ME.N := by rw [KernelMinusEnum.nums.2]; exact hi
  have hc := canE hi
  have hin : (allLt minusLGens.size fun k =>
      eqA 65 (compA 65 (minusEnum ()).pts[i]! minusLGens[k]!)
        (compA 65 minusLGens[k]! (minusEnum ()).pts[i]!)) =
      allN 5 fun k => Nat.beq (pm (ME.T i) (PL.G k)) (pm (PL.G k) (ME.T i)) := by
    rw [Bool.eq_iff_iff, allLt_iff, AI, bind.1]
    have e : ∀ k < 5, eqA 65 (compA 65 (minusEnum ()).pts[i]! minusLGens[k]!)
        (compA 65 minusLGens[k]! (minusEnum ()).pts[i]!) =
        Nat.beq (pm (ME.T i) (PL.G k)) (pm (PL.G k) (ME.T i)) := by
      intro k hk
      rw [ptE hN, bind.2 k hk, compA_unpack hc (canG hk), compA_unpack (canG hk) hc,
        eqA_unpack (canonK_pcomp hc (canG hk)) (canonK_pcomp (canG hk) hc)]
      rfl
    constructor
    · intro h k hk
      rw [← e k hk]
      exact h k hk
    · intro h k hk
      rw [e k hk]
      exact h k hk
  rw [hin, ptE hN, idA_eq KernelMinusEnum.kSz, eqA_unpack hc canI]
  exact cent_pt hi

theorem trans_ok : minusLTransCheck (minusEnum ()) = true := by
  unfold minusLTransCheck
  rw [allLt_iff]
  intro i hi
  have h := AI.1 kTrans i hi
  rw [anyN_eq, List.any_eq_true] at h
  obtain ⟨j, hj, e⟩ := h
  rw [List.any_eq_true]
  have hj' := List.mem_range.1 hj
  have hN : j < ME.N := by rw [KernelMinusEnum.nums.2]; exact hj'
  refine ⟨j, ?_, ?_⟩
  · rw [List.mem_range, KernelMinusEnum.minusEnum_pts, Array.size_ofFn]
    exact hN
  · rw [ptE hN, unpack_get' (by norm_num), beq_iff_eq]
    exact Nat.eq_of_beq_eq_true e

theorem bindX : locArr.size = 4 ∧ ∀ k < 4, locArr[k]! = unpack 65 7 (LX k) :=
  binds_of_check kBindX

theorem memX {k : ℕ} (hk : k < 4) :
    (minusLEnum ()).pts.toList.any (eqA 65 locArr[k]!) = true := by
  obtain ⟨j, hj, hx⟩ := memK_spec (AI.1 kMemX k hk)
  rw [List.any_eq_true]
  have hN : j < PL.N := by rw [nums.2]; exact hj
  refine ⟨unpack 65 7 (PL.T j), ?_, ?_⟩
  · rw [pinL, pts_toList (fun i => unpack 65 7 (PL.T i))]
    exact List.mem_map_of_mem (List.mem_range.2 hN)
  · rw [bindX.2 k hk, eqA_unpack (canX hk) (canL hj), hx, Nat.beq_refl]

theorem validX {k : ℕ} (hk : k < 4) : validA 65 locArr[k]! = true := by
  rw [bindX.2 k hk]
  exact validA_unpack (AI.1 kPermX k hk)

theorem loc0 : locArr[0]! = minusSylowA := rfl
theorem loc1 : locArr[1]! = minusSylowB := rfl
theorem loc2 : locArr[2]! = minusA5Gens[0]! := rfl
theorem loc3 : locArr[3]! = minusA5Gens[1]! := rfl

theorem local_ok : minusLLocalCheck (minusLEnum ()) = true := by
  unfold minusLLocalCheck
  rw [← loc0, ← loc1, ← loc2, ← loc3, memX (by norm_num), memX (by norm_num), memX (by norm_num),
    memX (by norm_num), validX (by norm_num), validX (by norm_num), validX (by norm_num),
    validX (by norm_num)]
  rfl

end CertificateChecks.KernelMinusL
