module

public import Certificates.Kernel.Sporadic.Co2Inv.Mats
public import Certificates.Kernel.Sporadic.Co2Inv.Bind
public import Certificates.Kernel.Sporadic.Co2.ChainA
public import Certificates.Kernel.Sporadic.Co2.FVecs
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.PosTableSound
public import CFSG.Certificates.Kernel.Spor.BindList
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

public section

namespace CertificateChecks.KernelSpor.Co2Inv

open CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.M1F2 CFSG.Sporadic.Co2Inv
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Certificates.Native

@[expose] noncomputable def vpChunk (k : Nat) : Bool :=
  bindFromK 22 VP ((Co2Faith.PL.drop (Nat.mul 100 k)).take 100) (Nat.mul 100 k)

@[expose] noncomputable def vpF (k : Nat) : Bool := vpChunk k

#kc_each_unfold vpF 0 23 as CertificateChecks.KernelSpor.Co2Inv.vp

#kc_forall_chunks vp_allK (fun k => vpChunk k = true) 23 CertificateChecks.KernelSpor.Co2Inv.vp 1

theorem vp_all : ∀ k < 23, vpChunk k = true := vp_allK

theorem PL_length : Co2Faith.PL.length = 2300 := by
  have h := Co2Faith.size_ok
  rwa [Co2Faith.packed_eq, List.size_toArray] at h

theorem vp_get {i : Nat} (hi : i < 2300) : co2PackedVecs[i]! = pg 22 (mask 22) VP i := by
  have hk : i / 100 < 23 := by omega
  have hj : i % 100 < ((Co2Faith.PL.drop (Nat.mul 100 (i / 100))).take 100).length := by
    rw [List.length_take, List.length_drop, PL_length]
    change i % 100 < min 100 (2300 - 100 * (i / 100))
    omega
  have h := bindFromK_spec (vp_all _ hk) (i % 100) hj
  have e : Nat.mul 100 (i / 100) + i % 100 = i := Nat.div_add_mod i 100
  rw [e, List.getElem_take, List.getElem_drop] at h
  rw [Co2Faith.packed_eq, getElem!_pos _ i (by rw [List.size_toArray, PL_length]; exact hi),
    List.getElem_toArray, ← h]
  congr 1
  exact e.symm

theorem unpack_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [getElem!_pos _ i (by simp [unpack, hi])]
  simp [unpack]

theorem gt0 : transposeRows 22 co2InvGens[0]! = unpackR 22 (WT 108) := by decide +kernel
theorem gt1 : transposeRows 22 co2InvGens[1]! = unpackR 22 (WT 109) := by decide +kernel
theorem gt2 : transposeRows 22 co2InvGens[2]! = unpackR 22 (WT 110) := by decide +kernel
theorem gt3 : transposeRows 22 co2InvGens[3]! = unpackR 22 (WT 111) := by decide +kernel
theorem gt4 : transposeRows 22 co2InvGens[4]! = unpackR 22 (WT 112) := by decide +kernel

theorem gt_eq : ∀ j < 5, transposeRows 22 co2InvGens[j]! = unpackR 22 (WT (108 + j)) := by
  intro j hj
  interval_cases j
  exacts [gt0, gt1, gt2, gt3, gt4]

theorem wf_gens : ∀ j < 5, wfRows co2InvGens[j]! = true := by
  intro j hj
  rw [gens_eq j hj]
  exact wfRows_unpack _

@[expose] noncomputable def vecK (j i : Nat) : Bool :=
  andK (Nat.blt (pg 12 (mask 12) (PT j) i) 2300)
    (Nat.beq (vmF 22 (WT (Nat.add 108 j)) (pg 22 (mask 22) VP i))
      (pg 22 (mask 22) VP (pg 12 (mask 12) (PT j) i)))

theorem vec0 : ∀ t < 2300, vecK 0 t = true := by kc_cover 100
theorem vec1 : ∀ t < 2300, vecK 1 t = true := by kc_cover 100
theorem vec2 : ∀ t < 2300, vecK 2 t = true := by kc_cover 100
theorem vec3 : ∀ t < 2300, vecK 3 t = true := by kc_cover 100
theorem vec4 : ∀ t < 2300, vecK 4 t = true := by kc_cover 100

theorem vec_all : ∀ j < 5, ∀ t < 2300, vecK j t = true := by
  intro j hj
  interval_cases j
  exacts [vec0, vec1, vec2, vec3, vec4]

theorem perm_all : allN 5 (fun j => invEqK 2300 12 (mask 12) (2300 * 12) (PT j) (PT (Nat.add 5 j))) =
    true := by quickRfl

theorem hi_all : allN 5 (fun j => Nat.beq (Nat.shiftRight (PT j) (2300 * 12)) 0) = true := by
  quickRfl

theorem sift0 : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2A.LR Co2A.TRI Co2A.BP 6 0
    (PT 0) = true := by quickRfl
theorem sift1 : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2A.LR Co2A.TRI Co2A.BP 6 0
    (PT 1) = true := by quickRfl
theorem sift2 : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2A.LR Co2A.TRI Co2A.BP 6 0
    (PT 2) = true := by quickRfl
theorem sift3 : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2A.LR Co2A.TRI Co2A.BP 6 0
    (PT 3) = true := by quickRfl
theorem sift4 : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2A.LR Co2A.TRI Co2A.BP 6 0
    (PT 4) = true := by quickRfl

theorem sift_all : ∀ j < 5, siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) Co2A.LR Co2A.TRI
    Co2A.BP 6 0 (PT j) = true := by
  intro j hj
  interval_cases j
  exacts [sift0, sift1, sift2, sift3, sift4]

theorem vec_facts {j : Nat} (hj : j < 5) {i : Nat} (hi : i < 2300) :
    pg 12 (mask 12) (PT j) i < 2300 ∧
      vecMulN 22 (transposeRows 22 co2InvGens[j]!) co2PackedVecs[i]! =
        co2PackedVecs[pg 12 (mask 12) (PT j) i]! := by
  have h := vec_all j hj i hi
  unfold vecK at h
  rw [andK_eq, Bool.and_eq_true] at h
  have ht := blt_iff.1 h.1
  refine ⟨ht, ?_⟩
  rw [gt_eq j hj, vecMulN_unpackR, vp_get hi, vp_get ht]
  exact Nat.eq_of_beq_eq_true h.2

theorem unpack_size (n w P : Nat) : (unpack n w P).size = n := by
  unfold unpack
  exact Array.size_ofFn

theorem genPerm_of {pt : Array UInt32} (hpt : ∀ i < 2300, (pt[co2PackedVecs[i]!]!).toNat = i)
    {j : Nat} (hj : j < 5) : genPermWith pt j = unpack 2300 12 (PT j) := by
  unfold genPermWith unpack
  change Array.ofFn (n := 2300) (fun i =>
      (pt[vecMulN 22 (transposeRows 22 co2InvGens[j]!) co2PackedVecs[i.val]!]!).toNat) =
    Array.ofFn (n := 2300) (fun i => pg 12 (mask 12) (PT j) i.val)
  refine congrArg (Array.ofFn (n := 2300)) (funext fun i => ?_)
  obtain ⟨ht, hv⟩ := vec_facts hj i.2
  rewrite [hv]
  exact hpt _ ht

theorem posTable_ok : ∀ i < 2300, (co2PosTable[co2PackedVecs[i]!]!).toNat = i := by
  have hpf := Co2Faith.packed_facts
  have hsz := Co2Faith.size_ok
  intro i hi
  exact CFSG.KC.PosTable.posTable_get (by rw [hsz]; exact fun k hk => (hpf k hk).1)
    (by rw [hsz]; exact fun a ha b hb e => (hpf a ha).2.2 b hb e) (by rw [hsz]; norm_num)
    (by rw [hsz]; exact hi)

theorem genPerm_eq {j : Nat} (hj : j < 5) : genPermWith co2PosTable j = unpack 2300 12 (PT j) :=
  genPerm_of posTable_ok hj

theorem genCheckOne_ok {j : Nat} (hj : j < 5) :
    genCheckOne (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable j = true := by
  have hp := allN_spec perm_all j hj
  have hh := allN_spec hi_all j hj
  obtain ⟨hinv, hisinv⟩ := invEqK_sound hp
  unfold genCheckOne
  rewrite [genPerm_eq hj]
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨wf_gens j hj, unpack_size _ _ _⟩, by rewrite [hinv]; exact hisinv⟩, fun i hi => ?_⟩, ?_⟩
  · rewrite [unpack_get hi, (vec_facts hj hi).2]
    exact rfl
  · exact siftK_soundR Co2A.binds Co2A.perm Co2A.hl rfl (Nat.eq_of_beq_eq_true hh)
      (range_of_permOK hp) (sift_all j hj)

theorem gens_check : gensCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable = true := by
  unfold gensCheck
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  exact ⟨rfl, fun j hj => genCheckOne_ok hj⟩

end CertificateChecks.KernelSpor.Co2Inv

end
