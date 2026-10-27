module

public import Certificates.Kernel.LocalComp.Fi24TwoB.Q15027
public import Certificates.Kernel.LocalComp.Fi24TwoB.L15027
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.RegIndexSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CertificateChecks.KernelSpor.Fi24C
open CertificateChecks.KernelSpor CertificateChecks.KernelLC
open CFSG.ComponentClassification.RankTwoSporadic.Cert (regIndex inRegs inRegs_regIndex_of_inj)
open CFSG.Sporadic.FischerOddCore (fi24T fi24KStrong treeConjN)
open CFSG.RankThree.Native (enumOK enumBfs keyA validA)

theorem eqA_refl (n : Nat) (a : Array Nat) : eqA n a a = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem idA_eq : idA 504 = unpack 504 9 (pidn 504 9) := (idK_sound kIdK).symm

theorem cnId : Cn 504 9 (pidn 504 9) := kIdC

theorem of_slices {L K : Nat} {f : Nat → Bool} (hL : 0 < L)
    (h : ∀ s < K, allN L (fun d => f (Nat.add (s * L) d)) = true) : ∀ i < K * L, f i = true := by
  intro i hi
  have hs : i / L < K := (Nat.div_lt_iff_lt_mul hL).2 hi
  have h1 := allN_spec (h (i / L) hs) (i % L) (Nat.mod_lt _ hL)
  have e : Nat.add (i / L * L) (i % L) = i := by
    rw [Nat.add_eq, Nat.mul_comm]
    exact Nat.div_add_mod i L
  rwa [e] at h1

theorem fi24T_eq : fi24T = Array.ofFn (n := 377 + 1) fun i => unpack 504 9 (Fi24ST.T i.val) := by
  unfold fi24T
  rw [kS, Fi24T.s0_eq, Fi24T.tree_eq, treeConj_eq]
  exact tree_facts.1

theorem fi24T_get {j : Nat} (hj : j < 378) : fi24T[j]! = unpack 504 9 (Fi24ST.T j) := by
  rw [fi24T_eq]
  exact ofFn1_get hj

theorem cnT {j : Nat} (hj : j < 378) : Cn 504 9 (Fi24ST.T j) := tree_facts.2.1 j hj

theorem basis_lt {k : Nat} (hk : k < 12) : fi24NBasis[k]! < 378 := by
  interval_cases k <;> decide

theorem gens_get {k : Nat} (hk : k < 12) : fi24NGens[k]! = unpack 504 9 (Fi24BN.G k) := by
  have e : fi24NGens[k]! = fi24T[fi24NBasis[k]!]! := by
    interval_cases k <;> rfl
  have h := (bAnd_iff _ _).1 (allN_spec Fi24BQ.kGens k hk)
  rw [e, fi24T_get (basis_lt hk), Nat.eq_of_beq_eq_true h.1]

theorem gens_perm : ∀ k < 12,
    permOK 504 9 (mask 9) (504 * 9) (Fi24BN.G k) (pinvS 504 9 (mask 9) (Fi24BN.G k)) = true :=
  fun k hk => ((bAnd_iff _ _).1 (allN_spec Fi24BQ.kGens k hk)).2

theorem cnG {k : Nat} (hk : k < 12) : Cn 504 9 (Fi24BN.G k) := by
  have h := Fi24BN.kHead
  simp only [Bool.and_eq_true] at h
  exact allN_spec h.1.1.1.2 k hk

theorem key_lt : ∀ p ∈ fi24NKey, p < 504 := fi24NKey_lt

theorem pts_eq : fi24NCert.pts = Array.ofFn (n := 4096) fun i => unpack 504 9 (Fi24BN.T i.val) :=
  enumBfs_pts_base fi24NGens_size (fun k hk => gens_get hk) Fi24BN.ok key_lt Fi24BN.keys
    (by decide)

theorem enum_ok : enumOK 504 fi24NGens fi24NKey fi24NCert = true :=
  enumOK_of_bfsK_base fi24NGens_size (fun k hk => gens_get hk) gens_perm Fi24BN.ok key_lt
    Fi24BN.keys (by decide)

theorem pts_size : fi24NCert.pts.size = 4096 := by rw [pts_eq]; simp

theorem pt_get {i : Nat} (hi : i < 4096) : fi24NCert.pts[i]! = unpack 504 9 (Fi24BN.T i) := by
  rw [pts_eq, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem cnN {i : Nat} (hi : i < 4096) : Cn 504 9 (Fi24BN.T i) := bfsK_canon Fi24BN.ok i hi

theorem ptKeys : ∀ a < fi24NCert.pts.size, ∀ b < fi24NCert.pts.size,
    keyA 504 fi24NKey fi24NCert.pts[a]! = keyA 504 fi24NKey fi24NCert.pts[b]! → a = b := by
  intro a ha b hb e
  rw [pts_size] at ha hb
  rw [pt_get ha, pt_get hb, keyA_unpack key_lt, keyA_unpack key_lt] at e
  exact keysSK_spec Fi24BN.keys a ha b hb e

theorem strongD {k : Nat} (hk : k < 16) : fi24KdStrong[k]! = unpack 504 9 (Fi24BKd.S k) := by
  rw [dS]
  exact ofFn_get hk

theorem cnD {k : Nat} (hk : k < 16) : Cn 504 9 (Fi24BKd.S k) ∧ Cn 504 9 (Fi24BKd.SI k) :=
  (bAnd_iff _ _).1 (allN_spec kCanD k hk)

theorem repD {k : Nat} (hk : k < 16) : Rep 504 fi24KdStrong[k]! (permOfArr 504 fi24KdStrong[k]!) :=
  CFSG.RankThree.Native.rep_of_validA (fi24KdStrong_valid chainsOK (by rw [sizeD]; exact hk))

theorem reps_get : fi24NOrbReps[0]! = unpack 504 9 (Fi24BX.R 0) ∧
    fi24NOrbReps[1]! = unpack 504 9 (Fi24ST.T 0) ∧ fi24NOrbReps[2]! = unpack 504 9 (Fi24BX.R 1) := by
  have hr : CFSG.Sporadic.FischerOddCore.rowsOf 504
      (CFSG.Sporadic.FischerOddCore.hexNums 3 fi24NRepText) =
      SA 504 9 2 Fi24BX.R := by
    rw [Fi24BT.rep_eq]
    exact rowsOf_unpack (by norm_num) (by norm_num)
      fun j hj => Nat.eq_of_beq_eq_true (allN_spec Fi24BX.kRows j hj)
  refine ⟨?_, ?_, ?_⟩
  · change (CFSG.Sporadic.FischerOddCore.rowsOf 504
      (CFSG.Sporadic.FischerOddCore.hexNums 3 fi24NRepText))[0]! = _
    rw [hr]
    exact ofFn_get (by norm_num)
  · exact fi24T_get (by norm_num)
  · change (CFSG.Sporadic.FischerOddCore.rowsOf 504
      (CFSG.Sporadic.FischerOddCore.hexNums 3 fi24NRepText))[1]! = _
    rw [hr]
    exact ofFn_get (by norm_num)

theorem cnR {i : Nat} (hi : i < 2) : Cn 504 9 (Fi24BX.R i) ∧
    permOK 504 9 (mask 9) (504 * 9) (Fi24BX.R i) (pinvS 504 9 (mask 9) (Fi24BX.R i)) = true :=
  (bAnd_iff _ _).1 (allN_spec Fi24BX.kRep i hi)

theorem conjA_eq (n : Nat) (g x : Array Nat) :
    CFSG.RankThree.Native.conjA n g x = CFSG.Sporadic.FischerOddCore.conjA n g x := rfl

theorem list_eq {tree rep : Array Nat} {N NS TF : Nat} {X : Nat → Nat}
    (htree : tree = unpack N 16 TF) (h0 : rep = unpack 504 9 (X 0)) (hc0 : Cn 504 9 (X 0))
    (hp0 : permOK 504 9 (mask 9) (504 * 9) (X 0) (pinvS 504 9 (mask 9) (X 0)) = true)
    (hN : N ≤ NS * 20)
    (hS : ∀ s < NS, stepSl 504 9 5 Fi24BKd.S Fi24BKd.SI X TF 16 N (s * 20) 20 = true) :
    fi24Conjs (fi24KdTreeElts tree) rep = (Array.ofFn (n := N + 1) fun i => unpack 504 9 (X i.val)) ∧
      ∀ i < N + 1, Cn 504 9 (X i) := by
  have hst := steps_of (n := 504) (w := 9) (r := 5) (N := N) (wt := 16) (NS := NS)
    (CH := 20) hN hS
  have hrep0 : Rep 504 (unpack 504 9 (X 0)) (permOfArr 504 (unpack 504 9 (X 0))) :=
    (rep_of_perm hp0).1
  have htv : ∀ i < tree.size, tree[i]! / 5 < i + 1 := by
    intro i hi
    have hi' : i < N := by rw [htree] at hi; simpa [unpack] using hi
    rw [htree, Fi24C.unpack_get' hi']
    exact (hst i hi').1
  have hc := conjs_eq (n := 504) (r := 5) (gens := fi24KdStrong) (rep := rep) (tree := tree)
    (by norm_num) (fun k hk => ⟨_, repD (by omega)⟩) ⟨_, by rw [h0]; exact hrep0⟩
    (by rw [h0]; simp [unpack]) htv
  have ht := treeConjN_eq (n := 504) (w := 9) (r := 5) (N := N) (wt := 16) (gens := fi24KdStrong)
    (s₀ := rep) (tree := tree) (GS := Fi24BKd.S) (GSI := Fi24BKd.SI) (T := X) (TF := TF)
    (by norm_num) (fun k hk => strongD (by omega)) (fun k hk => (cnD (by omega)).1)
    (fun k hk => (cnD (by omega)).2) (fun k hk => allN_spec permD k (by omega)) h0 hc0
    ⟨_, hrep0⟩ htree hst
  refine ⟨?_, ht.2.1⟩
  unfold fi24Conjs fi24KdTreeElts
  simp only [conjA_eq]
  rw [hc]
  exact ht.1

end CertificateChecks.KernelLC.Fi24B

end
