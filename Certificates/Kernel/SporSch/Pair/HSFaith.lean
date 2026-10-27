module

public import Certificates.Kernel.SporSch.Pair.HSCert
public import CFSG.Certificates.Kernel.SporSch.F2MatSound
public import CFSG.Certificates.Kernel.SporSch.PairClSound
public import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
meta import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
meta import Certificates.Data.CFSGNative.HS.Data
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.PHSSeedA CFSG.Sporadic.HS.Native.seedA

#ks_chars CertificateChecks.KernelSporSch.PHSSeedB CFSG.Sporadic.HS.Native.seedB

meta def CertificateChecks.KernelSporSch.hsMatsM : Array (Array Nat) :=
  let A := (CFSG.Sporadic.HS.Native.hsData ()).rowsA
  let B := (CFSG.Sporadic.HS.Native.hsData ()).rowsB
  #[A, B, CFSG.Sporadic.SmallF2.Native.transposeRows 20 A,
    CFSG.Sporadic.SmallF2.Native.transposeRows 20 B]

#kss_perms CertificateChecks.KernelSporSch.PHSM 20 CertificateChecks.KernelSporSch.hsMatsM

meta def CertificateChecks.KernelSporSch.hsSortM : Array (Array Nat) := Id.run do
  let bits := CertificateChecks.KernelSporSch.hsVA.map fun v =>
    (List.range 20).foldl (fun acc j => acc ||| (v[j]! <<< j)) 0
  let so := (Array.range 3850).qsort (fun a b => bits[a]! < bits[b]!)
  let mut soi := Array.replicate 3850 0
  for k in [0:3850] do
    soi := soi.set! so[k]! k
  return #[so, soi]

#kss_perms CertificateChecks.KernelSporSch.PHSSO 12 CertificateChecks.KernelSporSch.hsSortM

namespace CertificateChecks.KernelSporSch.PHSFaith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairF2
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch

@[expose] noncomputable def vmU (M v : Nat) : Nat :=
  (List.range 20).foldl (fun acc j => if v.testBit j then acc ^^^ pg 20 (mask 20) M j else acc) 0

@[expose] noncomputable def img (l i : Nat) : Nat := pg 12 (mask 12) (PHS l) i

@[expose] noncomputable def SO (i : Nat) : Nat := pg 12 (mask 12) (PHSSO 0) i

@[expose] noncomputable def SOI (i : Nat) : Nat := pg 12 (mask 12) (PHSSO 1) i

@[expose] noncomputable def BA : Array Nat := ((List.range 3850).map PHSVT).toArray

theorem ra : Nat.beq (payRun 20 PHSSeedA.chars 0 0 0) (PHSM 0) = true := by quickRfl
theorem rb : Nat.beq (payRun 20 PHSSeedB.chars 0 0 0) (PHSM 1) = true := by quickRfl

theorem tA : transposeRows 20 (unpack 20 20 (PHSM 0)) = unpack 20 20 (PHSM 2) := by
  decide +kernel

theorem tB : transposeRows 20 (unpack 20 20 (PHSM 1)) = unpack 20 20 (PHSM 3) := by
  decide +kernel

theorem vlt : allN 3850 (fun i => Nat.blt (PHSVT i) 1048576) = true := by quickRfl

theorem act : allN 3850 (fun i => PHSVT i != 0 && vmU (PHSM 2) (PHSVT i) == PHSVT (img 0 i) &&
    vmU (PHSM 3) (PHSVT i) == PHSVT (img 1 i)) = true := by
  decide +kernel

@[expose] noncomputable def srtB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64) (keySortAt [(3850, PHSVT)] SO SOI 3850) 64

theorem srt : ∀ g < 8, ∀ r < 8, srtB g r = true := by
  have h : allN 8 (fun g => allN 8 (fun r => srtB g r)) = true := by decide +kernel
  exact fun g hg r hr => allN_spec (allN_spec h g hg) r hr

theorem idx : hsBasisIdx.length = 20 ∧ ∀ k < 20, hsBasisIdx.getD k 0 < 3850 := by
  refine ⟨by decide, ?_⟩
  decide

theorem basis :
    (mulRows 20 (invRowsF2 20 (Array.ofFn (n := 20) fun k => PHSVT (hsBasisIdx.getD k.val 0)))
        (Array.ofFn (n := 20) fun k => PHSVT (hsBasisIdx.getD k.val 0)) == idRows 20 &&
      mulRows 20 (Array.ofFn (n := 20) fun k => PHSVT (hsBasisIdx.getD k.val 0))
        (invRowsF2 20 (Array.ofFn (n := 20) fun k => PHSVT (hsBasisIdx.getD k.val 0))) ==
        idRows 20) = true := by
  decide +kernel

theorem vecMulN_unpack (M v : Nat) : vecMulN 20 (unpack 20 20 M) v = vmU M v := by
  unfold vecMulN vmU
  apply List.foldl_ext
  intro acc j hj
  have hj' : j < 20 := List.mem_range.1 hj
  rw [Array.getElem?_eq_getElem (by simp [unpack]; omega), Option.getD_some]
  simp [unpack]

theorem rowsA_eq : CFSG.Sporadic.HS.Native.hsData.rowsA = unpack 20 20 (PHSM 0) := by
  have e : CFSG.Sporadic.HS.Native.hsData.rowsA = rowsOfPayload 20 CFSG.Sporadic.HS.Native.seedA :=
    rfl
  rw [e, PHSSeedA.eq, payRun_eq, Nat.eq_of_beq_eq_true ra]

theorem rowsB_eq : CFSG.Sporadic.HS.Native.hsData.rowsB = unpack 20 20 (PHSM 1) := by
  have e : CFSG.Sporadic.HS.Native.hsData.rowsB = rowsOfPayload 20 CFSG.Sporadic.HS.Native.seedB :=
    rfl
  rw [e, PHSSeedB.eq, payRun_eq, Nat.eq_of_beq_eq_true rb]

theorem bits_unpack {X : Nat} (hX : X < 2 ^ 20) : bitsOfList 20 (unpack 20 1 X).toList = X := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bitsOfList, CFSG.Sporadic.SmallF2.ofBits_testBit]
  by_cases hi : i < 20
  · rw [List.getD_eq_getElem _ _ (by simp [unpack]; exact hi)]
    simp only [hi, decide_true, Bool.true_and, Array.getElem_toList, unpack, Array.getElem_ofFn,
      pg, mask]
    have e1 : Nat.sub (Nat.shiftLeft 1 1) 1 = 1 := rfl
    have e2 : Nat.mul 1 i = i := Nat.one_mul i
    rw [e1, e2, Nat.testBit_eq_decide_div_mod_eq]
    change (((X >>> i) &&& 1) == 1) = decide (X / 2 ^ i % 2 = 1)
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    exact Bool.beq_eq_decide_eq _ _
  · simp only [hi, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by omega)
      (by omega)))).symm

theorem BA_get {i : Nat} (hi : i < 3850) : BA[i]! = PHSVT i := by
  rw [BA, getElem!_pos _ i (by simpa using hi)]
  simp

theorem bits_eq : hsVectors.map (bitsOfList 20) = BA := by
  have hV : hsVectors.size = 3850 := PairGen.hexVectors_size _ _ _
  apply Array.ext
  · simp [BA, hV]
  · intro i h1 h2
    have hi : i < 3850 := by simpa [hV] using h1
    have e := BA_get hi
    rw [getElem!_pos _ i h2] at e
    rw [e, Array.getElem_map]
    have hv := PHSCert.vget i hi
    rw [getElem!_pos _ i (by rw [hV]; exact hi)] at hv
    rw [hv]
    exact bits_unpack (Nat.blt_eq.mp (allN_spec vlt i hi))

theorem img_get (l : Nat) (hl : l < 8) (i : Nat) (hi : i < 3850) :
    (hsStrongArrs[l]!)[i]! = img l i ∧ img l i < 3850 := by
  have hI := (invEqK_sound (allN_spec PHSCert.perm l hl)).2
  rw [PHSCert.arr_eq l hl, PairGen.unpack_get hi]
  refine ⟨rfl, ?_⟩
  have := PairGen.lt_of_isInvA hI hi
  rwa [PairGen.unpack_get hi] at this

theorem mulA (v : Nat) : mulVecRows 20 CFSG.Sporadic.HS.Native.hsData.rowsA v = vmU (PHSM 2) v := by
  rw [rowsA_eq, mulVecRows, tA, vecMulN_unpack]

theorem mulB (v : Nat) : mulVecRows 20 CFSG.Sporadic.HS.Native.hsData.rowsB v = vmU (PHSM 3) v := by
  rw [rowsB_eq, mulVecRows, tB, vecMulN_unpack]

set_option maxHeartbeats 4000000 in
theorem facts : hsFaithfulWith hsVectors hsStrongArrs CFSG.Sporadic.HS.Native.hsData.rowsA
    CFSG.Sporadic.HS.Native.hsData.rowsB = true := by
  have c1 : allLt 3850 (fun i => BA[i]! != 0 &&
      mulVecRows 20 CFSG.Sporadic.HS.Native.hsData.rowsA BA[i]! == BA[(hsStrongArrs[0]!)[i]!]! &&
      mulVecRows 20 CFSG.Sporadic.HS.Native.hsData.rowsB BA[i]! == BA[(hsStrongArrs[1]!)[i]!]!) =
      true := by
    rw [allLt_iff]
    intro i hi
    obtain ⟨e0, l0⟩ := img_get 0 (by omega) i hi
    obtain ⟨e1, l1⟩ := img_get 1 (by omega) i hi
    rw [BA_get hi, e0, e1, BA_get l0, BA_get l1, mulA, mulB]
    exact allN_spec act i hi
  have c2 : strictInc BA.toList.mergeSort = true := by
    have h := keysK_sound (cs := [(3850, PHSVT)]) (SO := SO) (SOI := SOI) (nB := 8) (R := 8) (B := 64)
      (by simp) (by decide) srt
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, BA, List.toList_toArray]
      using h
  have hB : (Array.ofFn (n := 20) fun k => BA[hsBasisIdx.getD k.val 0]!) =
      Array.ofFn (n := 20) fun k => PHSVT (hsBasisIdx.getD k.val 0) := by
    refine congrArg (Array.ofFn (n := 20)) (funext fun k => ?_)
    exact BA_get (idx.2 k.val k.isLt)
  obtain ⟨c4, c5⟩ := (Bool.and_eq_true _ _).mp basis
  unfold hsFaithfulWith
  dsimp only
  rw [bits_eq, hB, c1, c2, c4, c5]
  rfl

end CertificateChecks.KernelSporSch.PHSFaith

end
