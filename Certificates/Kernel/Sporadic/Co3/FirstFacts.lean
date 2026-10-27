module

public import Certificates.Kernel.Sporadic.Co3.First
public import Certificates.Kernel.Sporadic.Co3.M
public import Certificates.Kernel.Sporadic.Co3.Sp36
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3First

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem nat_all_iff {n : Nat} {f : (i : Nat) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact ⟨fun H i h => H ⟨i, h⟩ (List.mem_finRange _), fun H x _ => H x.1 x.2⟩

theorem nat_any_iff {n : Nat} {f : (i : Nat) → i < n → Bool} :
    Nat.any n f = true ↔ ∃ i, ∃ h : i < n, f i h = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  exact ⟨fun ⟨x, _, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨i, h, hf⟩ => ⟨⟨i, h⟩, List.mem_finRange _, hf⟩⟩

theorem posIn_toArray (L : List Nat) (x : Nat) : posIn L.toArray x = L.idxOf x := by
  unfold posIn
  rw [List.findIdx?_toArray, List.size_toArray, ← List.findIdx_eq_getD_findIdx?, List.idxOf]

theorem restrictA_toArray (L : List Nat) (m : Array Nat) : restrictA L.toArray m = restrictArr L m := by
  apply Array.ext
  · simp [restrictA, restrictArr]
  · intro i h1 h2
    simp only [restrictA, restrictArr, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map,
      posIn_toArray]
    rw [getElem!_pos L.toArray i (by simpa [restrictA] using h1)]
    rfl

@[expose] noncomputable def commOK (i j T : Nat) : Bool :=
  bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3M.S i), bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3M.S j),
  bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3M.SI i), bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3M.SI j),
  bAnd(canonK 276 9 (mask 9) (276 * 9) T,
    Nat.beq T (pcomp 276 9 (mask 9) (pcomp 276 9 (mask 9) (pcomp 276 9 (mask 9) (Co3M.S j)
      (Co3M.S i)) (Co3M.SI j)) (Co3M.SI i)))))))

theorem comm_eq {i j k : Nat} (hi : i < 14) (hj : j < 14) (hk : k < 8)
    (h : commOK i j (Co3MComm.S k) = true) :
    eqA 276 co3MCommArrs[k]! (commA 276 co3MArrs i j) = true := by
  unfold commOK at h
  simp only [bAnd_iff] at h
  obtain ⟨ci, cj, cIi, cIj, cT, hT⟩ := h
  have pi := allN_spec Co3M.perm i hi
  have pj := allN_spec Co3M.perm j hj
  unfold commA
  rw [Co3M.arr_eq i hi, Co3M.arr_eq j hj, Co3MComm.arr_eq k hk, (invEqK_sound pi).1,
    (invEqK_sound pj).1, compA_unpack cj ci, compA_unpack (canonK_pcomp cj ci) cIj,
    compA_unpack (canonK_pcomp (canonK_pcomp cj ci) cIj) cIi,
    eqA_unpack cT (canonK_pcomp (canonK_pcomp (canonK_pcomp cj ci) cIj) cIi)]
  exact hT

theorem comm0 : commOK 1 4 (Co3MComm.S 0) = true := by quickRfl
theorem comm1 : commOK 1 5 (Co3MComm.S 1) = true := by quickRfl
theorem comm2 : commOK 1 6 (Co3MComm.S 2) = true := by quickRfl
theorem comm3 : commOK 2 3 (Co3MComm.S 3) = true := by quickRfl

theorem comms : ∀ k < 4, eqA 276 co3MCommArrs[k]!
    (commA 276 co3MArrs ((co3MCommPairs.getD k (0, 0)).1 - 1)
      ((co3MCommPairs.getD k (0, 0)).2 - 1)) = true := by
  intro k hk
  interval_cases k
  · exact comm_eq (i := 1) (j := 4) (by norm_num) (by norm_num) (by norm_num) comm0
  · exact comm_eq (i := 1) (j := 5) (by norm_num) (by norm_num) (by norm_num) comm1
  · exact comm_eq (i := 1) (j := 6) (by norm_num) (by norm_num) (by norm_num) comm2
  · exact comm_eq (i := 2) (j := 3) (by norm_num) (by norm_num) (by norm_num) comm3

@[expose] noncomputable def Csp : Nat := Co3Text36.L 82

@[expose] noncomputable def Kp (k : Nat) : Nat :=
  pcomp 36 6 (mask 6) (pcomp 36 6 (mask 6) Csp (restrictK 9 6 co3IzNat (Co3M.S k)))
    (pinvS 36 6 (mask 6) Csp)

theorem cspLine : allN 1 (fun j => Nat.beq Csp (Co3Text36.L (Nat.add 82 j))) = true := by
  quickRfl

theorem cspOK : bAnd(canonK 36 6 (mask 6) (36 * 6) Csp,
    bAnd(canonK 36 6 (mask 6) (36 * 6) (pinvS 36 6 (mask 6) Csp),
      permOK 36 6 (mask 6) (36 * 6) Csp (pinvS 36 6 (mask 6) Csp))) = true := by
  quickRfl

theorem csp_eq : co3CspArr = unpack 36 6 Csp :=
  (Co3Text36.field_of (f := 2) rfl (by norm_num) cspLine).2 0 (by norm_num)

theorem kOK : allN 7 (fun k => bAnd(canonK 276 9 (mask 9) (276 * 9) (Co3M.S k),
    canonK 36 6 (mask 6) (36 * 6) (restrictK 9 6 co3IzNat (Co3M.S k)))) = true := by
  quickRfl

theorem kappa_eq (k : Nat) (hk : k < 7) : co3KappaGens[k]! = unpack 36 6 (Kp k) := by
  obtain ⟨cS, cR⟩ := (bAnd_iff _ _).1 (allN_spec kOK k hk)
  obtain ⟨cC, cCI, pC⟩ := (by simpa only [bAnd_iff] using cspOK :
    canonK 36 6 (mask 6) (36 * 6) Csp = true ∧
      canonK 36 6 (mask 6) (36 * 6) (pinvS 36 6 (mask 6) Csp) = true ∧
      permOK 36 6 (mask 6) (36 * 6) Csp (pinvS 36 6 (mask 6) Csp) = true)
  have hsz : co3KappaGens.size = 7 := Array.size_ofFn
  rw [getElem!_pos co3KappaGens k (by omega)]
  unfold co3KappaGens
  rw [Array.getElem_ofFn, Co3M.arr_eq k (by omega), csp_eq]
  have hL : ∀ x ∈ co3IzNat, x < 276 := by decide
  have hlen : co3IzNat.length = 36 := rfl
  have e := restrictArr_unpack (w' := 6) cS hL (by rw [hlen]; norm_num)
  rw [hlen] at e
  rw [co3IzArr, restrictA_toArray, e]
  unfold renameA
  rw [compA_unpack cC cR, invCand_unpack pC, compA_unpack (canonK_pcomp cC cR) cCI]
  rfl

theorem coverOK : bAnd(Nat.beq (Kp 0) (pidn 36 6), bAnd(canonK 36 6 (mask 6) (36 * 6) (pidn 36 6),
    bAnd(idK 36 6 (mask 6),
    allN 6 (fun j => bAnd(Nat.beq (Kp (Nat.succ j)) (Co3M36.S j),
      canonK 36 6 (mask 6) (36 * 6) (Co3M36.S j)))))) = true := by
  quickRfl

theorem cover : coversOK 36 co3KappaGens (co3M36Arrs.extract 0 6) = true := by
  obtain ⟨h0, cid, hid, hj⟩ := (by simpa only [bAnd_iff] using coverOK :
    Nat.beq (Kp 0) (pidn 36 6) = true ∧ canonK 36 6 (mask 6) (36 * 6) (pidn 36 6) = true ∧
      idK 36 6 (mask 6) = true ∧
      allN 6 (fun j => bAnd(Nat.beq (Kp (Nat.succ j)) (Co3M36.S j),
        canonK 36 6 (mask 6) (36 * 6) (Co3M36.S j))) = true)
  have hgs : co3KappaGens.size = 7 := Array.size_ofFn
  have hM : co3M36Arrs.size = 16 := Co3M36.binds.2.2.2.1
  have hhs : (co3M36Arrs.extract 0 6).size = 6 := by simp [hM]
  have hh : ∀ j < 6, (co3M36Arrs.extract 0 6)[j]! = unpack 36 6 (Co3M36.S j) := by
    intro j hj
    rw [getElem!_pos _ j (by omega), Array.getElem_extract, ← getElem!_pos co3M36Arrs (0 + j)
      (by omega), Nat.zero_add, Co3M36.arr_eq j (by omega)]
  have key : ∀ j < 6, Kp (j + 1) = Co3M36.S j ∧ canonK 36 6 (mask 6) (36 * 6) (Co3M36.S j) = true :=
    fun j hjl => by
      obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec hj j hjl)
      exact ⟨Nat.eq_of_beq_eq_true a, b⟩
  have idA36 : idA 36 = unpack 36 6 (pidn 36 6) := (idK_sound hid).symm
  unfold coversOK allLt anyLt
  rw [Bool.and_eq_true, nat_all_iff, nat_all_iff]
  refine ⟨fun i hi => ?_, fun j hjl => ?_⟩
  · have hi7 : i < 7 := hgs ▸ hi
    rw [Bool.or_eq_true]
    rcases i with _ | j
    · left
      rw [kappa_eq 0 (by norm_num), Nat.eq_of_beq_eq_true h0, idA36, eqA_unpack cid cid,
        Nat.beq_refl]
    · right
      rw [nat_any_iff]
      have hj6 : j < 6 := by omega
      refine ⟨j, by rw [hhs]; exact hj6, ?_⟩
      beta_reduce
      rw [kappa_eq (j + 1) hi7, hh j hj6, (key j hj6).1, eqA_unpack (key j hj6).2 (key j hj6).2,
        Nat.beq_refl]
  · have hj6 : j < 6 := hhs ▸ hjl
    rw [nat_any_iff]
    refine ⟨j + 1, by rw [hgs]; omega, ?_⟩
    beta_reduce
    rw [kappa_eq (j + 1) (by omega), hh j hj6, (key j hj6).1,
      eqA_unpack (key j hj6).2 (key j hj6).2, Nat.beq_refl]

theorem siftOK : allN 6 (fun k => bAnd(Co3Text36.hiOK (Co3M36.S k), Co3Sp36.sift (Co3M36.S k))) =
    true := by
  quickRfl

theorem sifts : ∀ k < 6, siftA 36 co3Sp36Levels co3Sp36BaseArr 0 co3M36Arrs[k]! = true := by
  intro k hk
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec siftOK k hk)
  exact siftK_soundR Co3Sp36.binds Co3Sp36.perm Co3Sp36.hl (Co3M36.arr_eq k (by omega))
    (Nat.eq_of_beq_eq_true h1) (range_of_permOK (allN_spec Co3M36.perm k (by omega))) h2

theorem facts : (rawChainOK 276 (co3MCommArrs.extract 0 co3MCommGenCount) co3MCommArrs
        co3MCommBaseArr (wordsArr co3MCommGenCount co3MCommStrongCount co3MCommDerivations) 4 =
          true ∧
      rawOrbitSizes 276 co3MCommArrs co3MCommBaseArr = [240, 126, 32, 3]
    )
    ∧ (rawChainOK 36 (co3M36Arrs.extract 0 co3M36GenCount) co3M36Arrs co3M36BaseArr
        (wordsArr co3M36GenCount co3M36StrongCount co3M36Derivations) 4 = true ∧
      rawOrbitSizes 36 co3M36Arrs co3M36BaseArr = [36, 35, 18, 8, 4, 2]
    )
    ∧ ((∀ k < 4, eqA 276 co3MCommArrs[k]!
        (commA 276 co3MArrs ((co3MCommPairs.getD k (0, 0)).1 - 1)
          ((co3MCommPairs.getD k (0, 0)).2 - 1)) = true) ∧
      coversOK 36 co3KappaGens (co3M36Arrs.extract 0 6) = true ∧
      (∀ k < 6, siftA 36 co3Sp36Levels co3Sp36BaseArr 0 co3M36Arrs[k]! = true)
    ) :=
  ⟨⟨rawChainK_sound (NS := 18) (CH := 16) Co3MComm.binds Co3MComm.head Co3MComm.hl (by norm_num)
      Co3MComm.hs, by rw [rawOrbitSizesK_sound Co3MComm.binds Co3MComm.perm Co3MComm.hl]; decide⟩,
    ⟨rawChainK_sound (NS := 1) (CH := 36) Co3M36.binds Co3M36.head Co3M36.hl (by norm_num)
      Co3M36.hs, by rw [rawOrbitSizesK_sound Co3M36.binds Co3M36.perm Co3M36.hl]; decide⟩,
    comms, cover, sifts⟩

end CertificateChecks.KernelSpor.Co3First

end
