module

public import Certificates.Kernel.SporSch.Co2M.SixChain
public import CFSG.Sporadic.Co2Schreier.SixCheckInputs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

theorem allLt_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ i < n, f i = g i) : allLt n f = allLt n g := by
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, CFSG.Monster.B.Co2.allLt_iff]
  exact ⟨fun hf i hi => by rw [← h i hi]; exact hf i hi,
    fun hg i hi => by rw [h i hi]; exact hg i hi⟩

theorem basis_eq : witRec.wLocal.sixBasisIndices = [516, 1588, 1809, 1630, 312, 1801] ∧
    witRec.wLocal.sixAnchor = 29 := by
  decide +kernel

theorem sixIdx_lt (k : ℕ) : sixIdx k < 2300 := by
  unfold sixIdx
  rw [basis_eq.1, List.getD_eq_getElem?_getD]
  rcases h : [516, 1588, 1809, 1630, 312, 1801][k]? with _ | x
  · simp
  · have hx := List.mem_of_getElem? h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Option.getD_some]
    omega

theorem sixImage_rep {g : Array ℕ} {M M' : ℕ} (hg : MatRep.Rep 22 co2PackedVecs g M M') (k : ℕ) :
    sixImage g k = vmul 22 co2PackedVecs[sixIdx k]! M ^^^ vmul 22 co2PackedVecs[sixAnchorIdx]! M := by
  unfold sixImage
  have ha : sixAnchorIdx < co2PackedVecs.size := by
    rw [V_size, sixAnchorIdx, basis_eq.2]
    norm_num
  rw [(get_rep hg (by rw [V_size]; exact sixIdx_lt k)).2, (get_rep hg ha).2]

@[expose] noncomputable def cImgK : Bool :=
  allLt 2 (fun i => allLt 6 fun k =>
    vmul 22 co2PackedVecs[sixIdx k]! (cT.getD i (0, 0)).1 ^^^
      vmul 22 co2PackedVecs[sixAnchorIdx]! (cT.getD i (0, 0)).1 ==
    xorBits sixPacked (colBits (witRec.wLocal.sixRows.getD i []) k))

@[expose] noncomputable def qImgK : Bool :=
  allLt 8 (fun m => allLt 6 fun k =>
    vmul 22 co2PackedVecs[sixIdx k]! (qT.getD m (0, 0)).1 ^^^
      vmul 22 co2PackedVecs[sixAnchorIdx]! (qT.getD m (0, 0)).1 == sixPacked[k]!)

theorem cImg_ok : cImgK = true := by decide +kernel

theorem qImg_ok : qImgK = true := by decide +kernel

theorem c_len : cT.length = 2 := by rw [cT, List.length_map, cInitT, List.length_map, lens.1]

theorem q_len : qT.length = 8 := by
  have h : localRec.qWords.length = 8 := by decide +kernel
  rw [qT, List.length_map, h]

theorem rest_ok : (sixPacked.size == 6 && allLt 6 (fun k => decide (sixPacked[k]! < 2 ^ 22)) &&
    allLt 64 (fun m => m == 0 || xorBits sixPacked m != 0) &&
    allLt 6 (fun k => decide (sixIdx k < 2300)) && decide (sixAnchorIdx < 2300)) = true := by
  decide +kernel

theorem orig_ok : allLt 2 (fun i => allLt 63 fun p =>
    (witRec.wLocal.sixActionChain.origArrs[i]!)[p]! + 1 ==
      colMul (witRec.wLocal.sixRows.getD i []) (p + 1)) = true := by
  decide +kernel

theorem six_check : sixCheck witRec = true := by
  have hc : allLt 2 (fun i => allLt 6 fun k =>
      sixImage cArrs[i]! k == xorBits sixPacked (colBits (witRec.wLocal.sixRows.getD i []) k)) =
      true := by
    rw [← cImg_ok, cImgK]
    refine allLt_congr fun i hi => allLt_congr fun k _ => ?_
    rw [sixImage_rep (repT_get cRep (by rw [c_len]; exact hi)) k]
  have hq : allLt 8 (fun m => allLt 6 fun k => sixImage qArrs[m]! k == sixPacked[k]!) = true := by
    rw [← qImg_ok, qImgK]
    refine allLt_congr fun m hm => allLt_congr fun k _ => ?_
    rw [sixImage_rep (repT_get qRep (by rw [q_len]; exact hm)) k]
  have hr := rest_ok
  have hrec : recordOK 63 witRec.wLocal.sixActionChain 4 = true := Co2Six.record_ok
  have horb : recordOrbits 63 witRec.wLocal.sixActionChain = [63, 32, 15, 8, 3, 2] :=
    Co2Six.orbits_ok
  unfold sixCheck
  rw [hr, hc, hq, hrec, horb, orig_ok]
  rfl

end CertificateChecks.KernelSporSch.Co2M

end
