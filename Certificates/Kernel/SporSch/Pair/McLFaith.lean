module

public import Certificates.Kernel.SporSch.Pair.McLCert
public import Certificates.Kernel.Sporadic.McLK.Final
public import CFSG.Sporadic.Schreier.PairMcLFaithfulInputs
meta import CFSG.Sporadic.Schreier.PairMcLCertInputs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_perms CertificateChecks.KernelSporSch.PMcLVF 5 CertificateChecks.KernelSporSch.mclVA

namespace CertificateChecks.KernelSporSch.PMcLFaith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.F3R
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.F3.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor

@[expose] noncomputable def U (i : Nat) : List Nat := (unpack 21 5 (PMcLVF i)).toList

@[expose] noncomputable def VK (v : List Nat) : V := ofFnK 21 fun j => v.getD j 0

theorem vtab : hexTabK PMcLV.chars 1 21 5 275 PMcLVF = true := by quickRfl

theorem vget (i : Nat) (hi : i < 275) : mclVectors[i]! = U i :=
  PairGen.vec_get PMcLV.eq vtab i hi

theorem nz : allN 275 (fun i => (U i).any (· != 0)) = true := by decide +kernel

theorem dist : allN 275 (fun i => allN i (fun j => neK 21 5 (mask 5) 105 (PMcLVF i) (PMcLVF j))) =
    true := by quickRfl

theorem act : allN 275 (fun i =>
    bAnd((combK 21 McLK.ATM (VK (U i))).beq (VK (U (pg 9 (mask 9) (PMcL.S 0) i))),
      (combK 21 McLK.BTM (VK (U i))).beq (VK (U (pg 9 (mask 9) (PMcL.S 1) i))))) = true := by
  decide +kernel

theorem basis : (CFSG.Sporadic.J1.Native.wfM 21
    (CFSG.Sporadic.J1.Native.gaussInv 3 21 (CFSG.Sporadic.J1.Native.colMat 21 (mclBasisIdx.map U))) &&
    CFSG.Sporadic.J1.Native.mulL 3 21
      (CFSG.Sporadic.J1.Native.gaussInv 3 21 (CFSG.Sporadic.J1.Native.colMat 21 (mclBasisIdx.map U)))
      (CFSG.Sporadic.J1.Native.colMat 21 (mclBasisIdx.map U)) ==
      CFSG.Sporadic.J1.Native.idL 21) = true := by
  decide +kernel

theorem img (l : Nat) (hl : l < 13) (i : Nat) (hi : i < 275) :
    (mclStrongArrs[l]!)[i]! = pg 9 (mask 9) (PMcL.S l) i ∧ pg 9 (mask 9) (PMcL.S l) i < 275 := by
  have hI := (invEqK_sound (allN_spec PMcLCheck.perm l hl)).2
  rw [PMcLCheck.arr_eq l hl, PairGen.unpack_get hi]
  refine ⟨rfl, ?_⟩
  have := PairGen.lt_of_isInvA hI hi
  rwa [PairGen.unpack_get hi] at this

theorem mulA (v : V) : mulVecM 21 (CFSG.Sporadic.McL.Native.matA ()) v = combK 21 McLK.ATM v := by
  unfold mulVecM
  rw [McLK.tA, comb_eq]

theorem mulB (v : V) : mulVecM 21 (CFSG.Sporadic.McL.Native.matB ()) v = combK 21 McLK.BTM v := by
  unfold mulVecM
  rw [McLK.tB, comb_eq]

theorem vOf (v : List Nat) : vOfList 21 v = VK v := by
  unfold vOfList VK
  rw [ofFn_eq]

set_option maxHeartbeats 4000000 in
theorem facts : mclFaithfulWith mclVectors mclStrongArrs CFSG.Sporadic.McL.Native.matA
    CFSG.Sporadic.McL.Native.matB = true := by
  have hB : mclBasisIdx.map (fun i => mclVectors[i]!) = mclBasisIdx.map U :=
    List.map_congr_left fun i hi => vget i (by revert i hi; decide)
  have c1 : allLt 275 (fun i => mclVectors[i]!.any (· != 0)) = true := by
    rw [allLt_iff]
    intro i hi
    rw [vget i hi]
    exact allN_spec nz i hi
  have c2 : allLt 275 (fun i => allLt i fun j => mclVectors[i]! != mclVectors[j]!) = true := by
    rw [allLt_iff]
    intro i hi
    rw [allLt_iff]
    intro j hj
    rw [vget i hi, vget j (by omega)]
    exact bne_iff_ne.mpr (PairGen.vec_ne (allN_spec (allN_spec dist i hi) j hj))
  have c3 : allLt 275 (fun i =>
      (mulVecM 21 CFSG.Sporadic.McL.Native.matA (vOfList 21 mclVectors[i]!)).beq
        (vOfList 21 mclVectors[(mclStrongArrs[0]!)[i]!]!) &&
      (mulVecM 21 CFSG.Sporadic.McL.Native.matB (vOfList 21 mclVectors[i]!)).beq
        (vOfList 21 mclVectors[(mclStrongArrs[1]!)[i]!]!)) = true := by
    rw [allLt_iff]
    intro i hi
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec act i hi)
    obtain ⟨e0, l0⟩ := img 0 (by omega) i hi
    obtain ⟨e1, l1⟩ := img 1 (by omega) i hi
    rw [vget i hi, e0, e1, vget _ l0, vget _ l1, mulA, mulB, vOf, vOf, vOf, h1, h2]
    rfl
  obtain ⟨c4, c5⟩ := (Bool.and_eq_true _ _).mp basis
  unfold mclFaithfulWith mclBasisMatWith
  dsimp only
  rw [hB, c1, c2, c3, c4, c5]
  rfl

end CertificateChecks.KernelSporSch.PMcLFaith

end
