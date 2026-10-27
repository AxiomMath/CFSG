module

public import Certificates.Kernel.LocalComp.Fi24TwoB.F15027
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CertificateChecks.KernelSpor.Fi24C
open CertificateChecks.KernelSpor CertificateChecks.KernelLC
open CFSG.ComponentClassification.RankTwoSporadic.Cert (regIndex inRegs inRegs_regIndex_of_inj
  powA prodA)
open CFSG.Sporadic.FischerOddCore (fi24T fi24KStrong treeConjN)
open CFSG.RankThree.Native (enumOK enumBfs keyA validA)

theorem inRegs_ofFn {m : Nat} {X : Nat → Nat} {SK : List Nat}
    (hk : keysSK 504 9 [4, 0, 1, 2, 3, 6] m X SK = true) {j : Nat} (hj : j < m) :
    inRegs 504 fi24NKey (Array.ofFn (n := m) fun i => unpack 504 9 (X i.val))
      (regIndex 504 fi24NKey (Array.ofFn (n := m) fun i => unpack 504 9 (X i.val)))
      (unpack 504 9 (X j)) = true := by
  have hg : ∀ i < m, (Array.ofFn (n := m) fun i => unpack 504 9 (X i.val))[i]! = unpack 504 9 (X i) :=
    fun i hi => by rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  refine inRegs_regIndex_of_inj (fun a ha b hb e => ?_) (k := j) (by simpa using hj)
    (by rw [hg j hj]) (by rw [hg j hj]; exact eqA_refl _ _)
  simp only [Array.size_ofFn] at ha hb
  rw [hg a ha, hg b hb, keyA_unpack key_lt, keyA_unpack key_lt] at e
  exact keysSK_spec hk a ha b hb e

theorem inRegs_pts {i : Nat} (hi : i < 4096) :
    inRegs 504 fi24NKey fi24NCert.pts (regIndex 504 fi24NKey fi24NCert.pts)
      (unpack 504 9 (Fi24BN.T i)) = true := by
  rw [pts_eq]
  exact inRegs_ofFn Fi24BN.keys hi

@[expose] def Tl : Array (Array (Array Nat)) :=
  (Array.range 3).map fun o => fi24Conjs (fi24NOrbTrees.map fi24KdTreeElts)[o]! fi24NOrbReps[o]!

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] {f : α → β} {a : Array α} {i : Nat}
    (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem tl_get' {o : Nat} (ho : o < 3) :
    Tl[o]! = fi24Conjs (fi24KdTreeElts fi24NOrbTrees[o]!) fi24NOrbReps[o]! := by
  unfold Tl
  rw [map_get (by simpa using ho), getElem!_pos (Array.range 3) o (by simpa using ho),
    Array.getElem_range, map_get (by simpa [fi24NOrbTrees] using ho)]

theorem tl0 : Tl[0]! = (Array.ofFn (n := 1700 + 1) fun i => unpack 504 9 (Fi24BX.X 0 i.val)) ∧
    ∀ i < 1700 + 1, Cn 504 9 (Fi24BX.X 0 i) := by
  have hf := Fi24BX.kFirst
  simp only [Bool.and_eq_true] at hf
  have e : Fi24BX.X 0 0 = Fi24BX.R 0 := Nat.eq_of_beq_eq_true hf.1.1
  rw [tl_get' (by norm_num)]
  refine list_eq (NS := 85) (TF := Fi24BT.T0.F) Fi24BT.t0_eq ?_ ?_ ?_ (by norm_num)
    Fi24BX.st0All
  · rw [reps_get.1, e]
  · rw [e]
    exact (cnR (by norm_num)).1
  · rw [e]
    exact (cnR (by norm_num)).2

theorem tl1 : Tl[1]! = (Array.ofFn (n := 377 + 1) fun i => unpack 504 9 (Fi24BX.X 1 i.val)) ∧
    ∀ i < 377 + 1, Cn 504 9 (Fi24BX.X 1 i) := by
  have hf := Fi24BX.kFirst
  simp only [Bool.and_eq_true] at hf
  have e : Fi24BX.X 1 0 = Fi24ST.T 0 := Nat.eq_of_beq_eq_true hf.1.2
  have e0 : Fi24ST.T 0 = Fi24T.S0.F := Nat.eq_of_beq_eq_true s0T
  rw [tl_get' (by norm_num)]
  refine list_eq (NS := 19) (TF := Fi24BT.T1.F) Fi24BT.t1_eq ?_ ?_ ?_ (by norm_num)
    Fi24BX.st1All
  · rw [reps_get.2.1, e]
  · rw [e]
    exact cnT (by norm_num)
  · rw [e, e0]
    exact pS0

theorem tl2 : Tl[2]! = (Array.ofFn (n := 2015 + 1) fun i => unpack 504 9 (Fi24BX.X 2 i.val)) ∧
    ∀ i < 2015 + 1, Cn 504 9 (Fi24BX.X 2 i) := by
  have hf := Fi24BX.kFirst
  simp only [Bool.and_eq_true] at hf
  have e : Fi24BX.X 2 0 = Fi24BX.R 1 := Nat.eq_of_beq_eq_true hf.2
  rw [tl_get' (by norm_num)]
  refine list_eq (NS := 101) (TF := Fi24BT.T2.F) Fi24BT.t2_eq ?_ ?_ ?_ (by norm_num)
    Fi24BX.st2All
  · rw [reps_get.2.2, e]
  · rw [e]
    exact (cnR (by norm_num)).1
  · rw [e]
    exact (cnR (by norm_num)).2

theorem tl_get {o : Nat} (ho : o < 3) :
    Tl[o]! = (Array.ofFn (n := Fi24BQ.NM o) fun i => unpack 504 9 (Fi24BX.X o i.val)) ∧
      (∀ i < Fi24BQ.NM o, Cn 504 9 (Fi24BX.X o i)) ∧
      keysSK 504 9 [4, 0, 1, 2, 3, 6] (Fi24BQ.NM o) (Fi24BX.X o) (Fi24BX.SK o) = true := by
  interval_cases o
  · exact ⟨tl0.1, tl0.2, Fi24BX.keys0⟩
  · exact ⟨tl1.1, tl1.2, Fi24BX.keys1⟩
  · exact ⟨tl2.1, tl2.2, Fi24BX.keys2⟩

theorem tl_size : Tl.size = 3 := by simp [Tl]

theorem inRegs_tl {o j : Nat} (ho : o < 3) (hj : j < Fi24BQ.NM o) :
    inRegs 504 fi24NKey Tl[o]! (Tl.map (regIndex 504 fi24NKey))[o]! (unpack 504 9 (Fi24BX.X o j)) =
      true := by
  rw [map_get (by rw [tl_size]; exact ho), (tl_get ho).1]
  exact inRegs_ofFn (tl_get ho).2.2 hj

theorem elts_foldl :
    ∀ (L : List Nat) (A : Array (Array Nat)), (∀ j < A.size, ∃ g ∈ fi24Kd, Rep 504 A[j]! g) →
      (∀ i < L.length, L[i]! / 5 < A.size + i) →
      ∀ j < (L.foldl (fun acc t => acc.push (compA 504 fi24KdStrong[t % 5]! acc[t / 5]!)) A).size,
        ∃ g ∈ fi24Kd, Rep 504
          (L.foldl (fun acc t => acc.push (compA 504 fi24KdStrong[t % 5]! acc[t / 5]!)) A)[j]! g
  | [], _, hA, _ => hA
  | t :: L, A, hA, hL => by
    rw [List.foldl_cons]
    have ht : t / 5 < A.size := by
      have := hL 0 (by simp)
      simpa using this
    refine elts_foldl L _ (fun j hj => ?_) (fun i hi => ?_)
    · rw [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [getElem!_pos _ j (by simp; omega), Array.getElem_push_lt hj, ← getElem!_pos A j hj]
        exact hA j hj
      · rw [getElem!_pos _ A.size (by simp), Array.getElem_push_eq]
        obtain ⟨g, hg, hr⟩ := hA (t / 5) ht
        have hk : t % 5 < 5 := Nat.mod_lt _ (by norm_num)
        exact ⟨_, fi24Kd.mul_mem (permOfArr_mem_fi24Kd chainsOK hk) hg,
          rep_compA (repD (by omega)) hr⟩
    · have := hL (i + 1) (by simp; omega)
      rw [Array.size_push]
      simp only [List.getElem!_cons_succ] at this
      omega

theorem elts_mem {tree : Array Nat} (ht : ∀ i < tree.size, tree[i]! / 5 < i + 1) :
    ∀ j < (fi24KdTreeElts tree).size, ∃ g ∈ fi24Kd, Rep 504 (fi24KdTreeElts tree)[j]! g := by
  unfold fi24KdTreeElts
  rw [← Array.foldl_toList]
  refine elts_foldl tree.toList #[idA 504] (fun j hj => ⟨1, fi24Kd.one_mem, ?_⟩) (fun i hi => ?_)
  · have : j = 0 := by simpa using hj
    subst this
    exact rep_idA
  · have hi' : i < tree.size := by simpa using hi
    have e : tree.toList[i]! = tree[i]! := by
      rw [getElem!_pos _ i hi, getElem!_pos tree i hi', Array.getElem_toList]
    have e1 : (#[idA 504] : Array (Array Nat)).size = 1 := rfl
    rw [e, e1]
    have := ht i hi'
    omega

theorem tree_valid {N NS TF : Nat} {X : Nat → Nat} {tree : Array Nat} (htree : tree = unpack N 16 TF)
    (hN : N ≤ NS * 20)
    (hS : ∀ s < NS, stepSl 504 9 5 Fi24BKd.S Fi24BKd.SI X TF 16 N (s * 20) 20 = true) :
    ∀ i < tree.size, tree[i]! / 5 < i + 1 := by
  have hst := steps_of (n := 504) (w := 9) (r := 5) (N := N) (wt := 16) (NS := NS) (CH := 20) hN hS
  intro i hi
  have hi' : i < N := by rw [htree] at hi; simpa [unpack] using hi
  rw [htree, Fi24C.unpack_get' hi']
  exact (hst i hi').1

theorem trees_valid {o : Nat} (ho : o < 3) :
    ∀ i < (fi24NOrbTrees[o]!).size, (fi24NOrbTrees[o]!)[i]! / 5 < i + 1 := by
  interval_cases o
  · exact tree_valid (NS := 85) Fi24BT.t0_eq (by norm_num) Fi24BX.st0All
  · exact tree_valid (NS := 19) Fi24BT.t1_eq (by norm_num) Fi24BX.st1All
  · exact tree_valid (NS := 101) Fi24BT.t2_eq (by norm_num) Fi24BX.st2All

theorem sift_of_mem {g : Array Nat} {G : Equiv.Perm (Fin 504)} (hG : Rep 504 g G) (hm : G ∈ fi24Kd) :
    siftA 504 fi24KdLevels fi24KdBase.toArray 0 g = true :=
  (siftA_iff_mem_originalSubgroup (fi24KdChain_arrays chainsOK) (by norm_num)
    (fi24KdChainsOK_facts chainsOK).2.2.1 hG).2 hm

end CertificateChecks.KernelLC.Fi24B

end
