module

public import Certificates.Data.Kernel.HN1408Blk
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockCheck
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.L34InvSound
public import Certificates.Kernel.HN1408.Glue

set_option maxRecDepth 4000

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin CFSG.KC.Blk
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.KLie.CT (andB orB notB anyN)

theorem bget {B p : Nat} (hp : p < 1408) : (unpack 1408 4 B)[p]! = pg 4 (mask 4) B p :=
  CFSG.KC.Misc.PairCount.unpack_get hp

theorem tap {T p : Nat} (hT : Cn T) (hp : p < 1408) :
    ap (tabT (unpack 1408 11 T)) p = pg 11 (mask 11) T p := by
  rw [ap_tabT _ (unpack_lt hT), CFSG.KC.Misc.PairCount.unpack_get hp]

theorem tlt {T p : Nat} (hT : Cn T) (hp : p < 1408) : pg 11 (mask 11) T p < 1408 :=
  CFSG.KC.L34KSnd.canon_lt hT hp

theorem lap {k L b : Nat} (hL : canonK k 4 (mask 4) (k * 4) L = true) (hb : b < k) :
    ap (tabT (unpack k 4 L)) b = pg 4 (mask 4) L b := by
  rw [ap_tabT _ (unpack_lt hL), CFSG.KC.Misc.PairCount.unpack_get hb]

theorem allN_iff' {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  CFSG.KS.Raw.Orb.allN_iff

theorem blkMapOK_of {k B T L : Nat} (hT : Cn T) (hL : canonK k 4 (mask 4) (k * 4) L = true)
    (h : blkMapK 1408 11 4 B k T L = true) :
    blkMapOK k (unpack 1408 4 B) (tabT (unpack 1408 11 T)) (tabT (unpack k 4 L)) = true := by
  unfold blkMapOK
  rw [CFSG.KS.TW.allIn_iff]
  intro p hp
  have h1 := allN_iff'.1 h p hp
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h1
  rw [bget hp, tap hT hp, bget (tlt hT hp)]
  by_cases hb : pg 4 (mask 4) B p < k
  · rw [if_pos hb, lap hL hb]
    rw [show Nat.blt (pg 4 (mask 4) B p) k = true from Nat.blt_eq.mpr hb] at h1
    simp only [beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h1
  · rw [if_neg hb]
    rw [show Nat.blt (pg 4 (mask 4) B p) k = false from
      Bool.eq_false_iff.2 fun h => hb (Nat.blt_eq.mp h)] at h1
    simpa using Nat.le_of_ble_eq_true h1

theorem blkTrivOK_eq {B T : Nat} (hT : Cn T) :
    blkTrivOK (unpack 1408 4 B) (tabT (unpack 1408 11 T)) = blkTrivK 1408 11 4 B T := by
  rw [Bool.eq_iff_iff]
  unfold blkTrivOK blkTrivK
  rw [CFSG.KS.TW.allIn_iff, allN_iff']
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  rw [bget hp, tap hT hp, bget (tlt hT hp), beq_iff_eq, Nat.beq_eq]

theorem blkLe_of {k B : Nat} (h : blkLeK 1408 4 B k = true) :
    (unpack 1408 4 B).all (· ≤ k) = true := by
  have hg : ∀ p < 1408, (unpack 1408 4 B)[p]! = pg 4 (mask 4) B p := fun p hp => bget hp
  have hsz : (unpack 1408 4 B).size = 1408 := CFSG.KC.L34KSnd.size_unpack B
  generalize unpack 1408 4 B = A at hg hsz ⊢
  rw [Array.all_eq_true]
  intro p hp
  have hp' : p < 1408 := by rwa [hsz] at hp
  rw [← getElem!_pos _ p hp, hg p hp']
  have := allN_iff'.1 h p hp'
  simpa using Nat.le_of_ble_eq_true this

theorem blkSurjOK_of {k B : Nat} (h : blkSurjK 1408 4 B k = true) :
    blkSurjOK k (unpack 1408 4 B) = true := by
  have hg : ∀ p < 1408, (unpack 1408 4 B)[p]! = pg 4 (mask 4) B p := fun p hp => bget hp
  have hsz : (unpack 1408 4 B).size = 1408 := CFSG.KC.L34KSnd.size_unpack B
  generalize unpack 1408 4 B = A at hg hsz ⊢
  unfold blkSurjOK
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  obtain ⟨p, hp, e⟩ := CFSG.KC.L34Inv.anyN_iff.1 (allN_iff'.1 h j hj')
  rw [Array.any_eq_true]
  have hp' : p < A.size := by rw [hsz]; exact hp
  refine ⟨p, hp', ?_⟩
  rw [← getElem!_pos _ p hp', hg p hp, beq_iff_eq]
  exact Nat.eq_of_beq_eq_true e

theorem blk_eq {s : String} {cs : List Char} {B : Nat} (hs : s = String.ofList cs)
    (h : bindListK 1408 4 B (cs.map fun c => c.toNat - 48) = true) :
    blkOfString s = unpack 1408 4 B := by
  unfold blkOfString
  rw [hs, String.toList_ofList]
  have := eq_unpack_of_bindListK (A := (cs.map fun c => c.toNat - 48).toArray) (by simpa using h)
  exact this

end CFSG.KD.HN1408

end
