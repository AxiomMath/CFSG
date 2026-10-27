
module

public import Certificates.Kernel.SporSch.Pair.J2Chain
public import Certificates.Kernel.SporSch.Pair.GenCertK
public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Sporadic.Schreier.PairJ2FaithfulInputs
meta import CFSG.Sporadic.Schreier.PairJ2CertInputs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

meta def CertificateChecks.KernelSporSch.j2VA : Array (Array Nat) :=
  CFSG.Sporadic.Schreier.j2Vectors.map List.toArray

#kss_perms CertificateChecks.KernelSporSch.PJ2VT 4 CertificateChecks.KernelSporSch.j2VA

#ks_chars CertificateChecks.KernelSporSch.PJ2V CFSG.Sporadic.Schreier.j2VectorsHex

namespace CertificateChecks.KernelSporSch.PJ2Faith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.J1.Native
open CertificateChecks.KernelSporSch

@[expose] noncomputable def U (i : Nat) : List Nat := (unpack 14 4 (PJ2VT i)).toList

theorem vtab : hexTabK PJ2V.chars 1 14 4 315 PJ2VT = true := by quickRfl

theorem vget (i : Nat) (hi : i < 315) : j2Vectors[i]! = U i :=
  PairGen.vec_get PJ2V.eq vtab i hi

theorem nz : allN 315 (fun i => (U i).any (· != 0)) = true := by decide +kernel

theorem dist : allN 315 (fun i => allN i (fun j => neK 14 4 (mask 4) 56 (PJ2VT i) (PJ2VT j))) =
    true := by quickRfl

theorem act : allN 315 (fun i =>
    bAnd(mvL 5 (CFSG.Sporadic.J2.Native.mA ()) (U i) == U (pg 9 (mask 9) (PJ2.S 0) i),
      mvL 5 (CFSG.Sporadic.J2.Native.mB ()) (U i) == U (pg 9 (mask 9) (PJ2.S 1) i))) = true := by
  decide +kernel

theorem basis : (wfM 14 (gaussInv 5 14 (colMat 14 (j2BasisIdx.map U))) &&
    mulL 5 14 (gaussInv 5 14 (colMat 14 (j2BasisIdx.map U))) (colMat 14 (j2BasisIdx.map U)) ==
      idL 14) = true := by
  decide +kernel

theorem img (l : Nat) (hl : l < 7) (i : Nat) (hi : i < 315) :
    ((j2StrongArrs ())[l]!)[i]! = pg 9 (mask 9) (PJ2.S l) i ∧ pg 9 (mask 9) (PJ2.S l) i < 315 := by
  have hI := (invEqK_sound (allN_spec PJ2.perm l hl)).2
  rw [PJ2.arr_eq l hl, PairGen.unpack_get hi]
  refine ⟨rfl, ?_⟩
  have := PairGen.lt_of_isInvA hI hi
  rwa [PairGen.unpack_get hi] at this

set_option maxHeartbeats 4000000 in
theorem facts : j2FaithfulOK = true := by
  have hB : j2BasisIdx.map (fun i => j2Vectors[i]!) = j2BasisIdx.map U :=
    List.map_congr_left fun i hi => vget i (by revert i hi; decide)
  have c1 : allLt 315 (fun i => j2Vectors[i]!.any (· != 0)) = true := by
    rw [allLt_iff]
    intro i hi
    rw [vget i hi]
    exact allN_spec nz i hi
  have c2 : allLt 315 (fun i => allLt i fun j => j2Vectors[i]! != j2Vectors[j]!) = true := by
    rw [allLt_iff]
    intro i hi
    rw [allLt_iff]
    intro j hj
    rw [vget i hi, vget j (by omega)]
    exact bne_iff_ne.mpr (PairGen.vec_ne (allN_spec (allN_spec dist i hi) j hj))
  have c3 : allLt 315 (fun i =>
      mvL 5 CFSG.Sporadic.J2.Native.mA j2Vectors[i]! == j2Vectors[(j2StrongArrs[0]!)[i]!]! &&
      mvL 5 CFSG.Sporadic.J2.Native.mB j2Vectors[i]! == j2Vectors[(j2StrongArrs[1]!)[i]!]!) =
      true := by
    rw [allLt_iff]
    intro i hi
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec act i hi)
    obtain ⟨e0, l0⟩ := img 0 (by omega) i hi
    obtain ⟨e1, l1⟩ := img 1 (by omega) i hi
    rw [vget i hi, e0, e1, vget _ l0, vget _ l1, h1, h2]
    rfl
  obtain ⟨c4, c5⟩ := (Bool.and_eq_true _ _).mp basis
  unfold j2FaithfulOK j2BasisInv j2BasisMat
  rw [hB, c1, c2, c3, c4, c5]
  rfl

end CertificateChecks.KernelSporSch.PJ2Faith

end
