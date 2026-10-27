module

public import Certificates.Kernel.PSL26.Checks
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.LevelTrSound
public import CFSG.Certificates.Kernel.Item434.PkSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Quasithin.Recognition.RuRank3PSLInputs
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Certificates.NativeSchreierEnum
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPSL26

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin CFSG.KC.Item434
open CFSG.KC.B3S3K (cm pw)
open CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native
open CFSG.Monster.B.Co2 (allLt_iff)

theorem allN_get {m : ℕ} {f : ℕ → Bool} (h : allN m f = true) {i : ℕ} (hi : i < m) : f i = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 h i hi

theorem c7044B : (Nat.beq psl26Strong.size 9 &&
    allN 9 fun k => bindArrK psl26Strong[k]! 26 5 (P26.S k)) = true := by quickRfl

theorem c7044G : bindArrK psl26X 26 5 (P26.S 0) = true ∧ bindArrK psl26S 26 5 (P26.S 1) = true ∧
    bindArrK psl26T 26 5 (P26.S 2) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem c7044D : (Nat.beq psl26D.size 26 && allN 26 fun k => bindArrK psl26D[k]! 26 5 (PD k)) =
    true := by quickRfl

theorem c7044N5 : bindArrK psl26D[1]! 26 5 (PD 2) = false := by decide +kernel

theorem bindsP : Binds 26 5 P26.S 9 3 P26.BP psl26Strong (ruBaseArr 26 [0, 1, 2]) :=
  ⟨by norm_num, by norm_num, by norm_num, (binds_of_check c7044B).1, (binds_of_check c7044B).2,
    by simp [ruBaseArr], fun t ht => Nat.eq_of_beq_eq_true (allN_get c7044BP ht)⟩

theorem cnt : rcnt (P26.LR 0) = 26 ∧ rcnt (P26.LR 1) = 25 ∧ rcnt (P26.LR 2) = 12 := by
  obtain ⟨h0, h1, h2⟩ := c7044C
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem levP {i : ℕ} (hi : i < 3) :
    (rawLevels 26 psl26Strong (ruBaseArr 26 [0, 1, 2]))[i]!.pts.size = rcnt (P26.LR i) ∧
      ∀ k < rcnt (P26.LR i), (rawLevels 26 psl26Strong (ruBaseArr 26 [0, 1, 2]))[i]!.tr[k]! =
        unpack 26 5 (trP i k) :=
  levelTr_sound bindsP P26.head P26.hl hi

theorem pkS {k : ℕ} (hk : k < 9) : Pk 26 5 psl26Strong[k]! (P26.S k) :=
  ⟨(binds_of_check c7044B).2 k hk, allN_get c7044PB hk⟩

theorem pkX : Pk 26 5 psl26X (P26.S 0) :=
  ⟨unpack_eq_of_bindArrK c7044G.1, allN_get c7044PB (by norm_num)⟩

theorem pkSs : Pk 26 5 psl26S (P26.S 1) :=
  ⟨unpack_eq_of_bindArrK c7044G.2.1, allN_get c7044PB (by norm_num)⟩

theorem pkT : Pk 26 5 psl26T (P26.S 2) :=
  ⟨unpack_eq_of_bindArrK c7044G.2.2, allN_get c7044PB (by norm_num)⟩

theorem pkD {k : ℕ} (hk : k < 26) : Pk 26 5 psl26D[k]! (PD k) :=
  ⟨(binds_of_check c7044D).2 k hk, allN_get c7044DP hk⟩

theorem powArr_eq (n : ℕ) (t : Array ℕ) :
    ∀ k, CFSG.Quasithin.RuRank3.powArr n t k = CFSG.Monster.B.Mathieu.powArr n t k
  | 0 => rfl
  | k + 1 => by
    rw [CFSG.Quasithin.RuRank3.powArr, CFSG.Monster.B.Mathieu.powArr, powArr_eq n t k]

theorem ofFn_tr3 {L : Array Level} {a b c : ℕ} {A B C : Array ℕ} (hA : L[0]!.tr[a]! = A)
    (hB : L[1]!.tr[b]! = B) (hC : L[2]!.tr[c]! = C) (hr : ∀ p < 26, C[p]! < 26) :
    Array.ofFn (n := 26) (fun p => tr3 L a b c p.val) = compA 26 (compA 26 A B) C := by
  unfold compA
  refine congrArg (Array.ofFn (n := 26)) (funext fun p => ?_)
  rw [getElem!_pos (Array.ofFn (n := 26) fun j : Fin 26 => A[B[j.val]!]!) (C[p.val]!)
    (by rw [Array.size_ofFn]; exact hr p.val p.2), Array.getElem_ofFn]
  unfold tr3
  rw [hA, hB, hC]

theorem rg {i k : ℕ} (h : rgP (trP i k) = true) :
    Pk 26 5 (unpack 26 5 (trP i k)) (trP i k) ∧ ∀ p < 26, (unpack 26 5 (trP i k))[p]! < 26 := by
  unfold rgP at h
  rw [Bool.and_eq_true] at h
  refine ⟨⟨rfl, h.1⟩, fun p hp => ?_⟩
  rw [CFSG.KC.BfsPin.unpack_getElem!, if_pos hp]
  simpa using allN_get h.2 hp

theorem ordRow_all {a : ℕ} (ha : a < 26) : ordRow a = true := by
  rcases (by omega : a < 7 ∨ (7 ≤ a ∧ a < 14) ∨ (14 ≤ a ∧ a < 20) ∨ 20 ≤ a) with h | h | h | h
  · exact allN_get c7044O0 h
  · have e := allN_get c7044O1 (i := a - 7) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_cancel' h.1] at e
  · have e := allN_get c7044O2 (i := a - 14) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_cancel' h.1] at e
  · have e := allN_get c7044O3 (i := a - 20) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_cancel' h] at e

theorem orders : psl26OrdersOK psl26Levels = true := by
  have hw := c7044W
  have eL : psl26Levels = rawLevels 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) := rfl
  obtain ⟨n0, n1, n2⟩ := cnt
  have hT := c7044T
  unfold trOK at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨t1, t2⟩, t3⟩ := hT
  unfold psl26OrdersOK
  rw [eL]
  refine allLt_iff.2 fun a ha => allLt_iff.2 fun b hb => allLt_iff.2 fun c hc => ?_
  dsimp only
  have tA := (levP (i := 0) (by norm_num)).2 a (by rw [n0]; exact ha)
  have tB := (levP (i := 1) (by norm_num)).2 b (by rw [n1]; exact hb)
  have tC := (levP (i := 2) (by norm_num)).2 c (by rw [n2]; exact hc)
  obtain ⟨pA, -⟩ := rg (allN_get t1 ha)
  obtain ⟨pB, -⟩ := rg (allN_get t2 hb)
  obtain ⟨pC, rC⟩ := rg (allN_get t3 hc)
  have pG := pk_comp hw (pk_comp hw pA pB) pC
  rw [ofFn_tr3 tA tB tC rC, powArr_eq, powArr_eq, powArr_eq,
    eqA_pk hw (pk_powArr hw pG 12) (pk_id hw), eqA_pk hw (pk_powArr hw pG 13) (pk_id hw),
    eqA_pk hw (pk_powArr hw pG 5) (pk_id hw)]
  exact allN_get (allN_get (ordRow_all ha) hb) hc

theorem closed {a : Array ℕ} {A o : ℕ} (hA : Pk 26 5 a A) (h : clK A o = true) :
    psl26DClosed a = true := by
  have hw := c7044W
  have hs : psl26D.size = 26 := (binds_of_check c7044D).1
  unfold psl26DClosed
  refine allLt_iff.2 fun i hi => ?_
  have hc := allN_get h hi
  rw [Bool.and_eq_true] at hc
  have hlt : DW (o + i) < 26 := by simpa using hc.1
  rw [Array.any_eq_true]
  refine ⟨DW (o + i), by rw [hs]; exact hlt, ?_⟩
  rw [← getElem!_pos psl26D (DW (o + i)) (by rw [hs]; exact hlt),
    eqA_pk hw (pkD hlt) (pk_comp hw hA (pkD hi))]
  exact hc.2

theorem avoidT : (psl26D.all fun e => !eqA 26 e psl26T) = true := by
  have hw := c7044W
  have hs : psl26D.size = 26 := (binds_of_check c7044D).1
  rw [Array.all_eq_true]
  intro i hi
  rw [hs] at hi
  rw [← getElem!_pos psl26D i (by rw [hs]; exact hi), eqA_pk hw (pkD hi) pkT]
  exact allN_get c7044A.1 hi

theorem rel : psl26RelOK = true := by
  have hw := c7044W
  unfold psl26RelOK
  rw [powArr_eq, powArr_eq, powArr_eq, eqA_pk hw (pk_powArr hw pkX 13) (pk_id hw),
    eqA_pk hw pkX (pk_id hw), eqA_pk hw (pk_powArr hw pkSs 2) (pk_id hw),
    eqA_pk hw pkSs (pk_id hw), eqA_pk hw (pk_powArr hw pkT 2) (pk_id hw),
    eqA_pk hw pkT (pk_id hw),
    eqA_pk hw (pk_comp hw (pk_comp hw (pk_comp hw pkSs pkX) pkSs) pkX) (pk_id hw),
    eqA_pk hw (pk_comp hw pkT pkSs) (pk_comp hw pkSs pkT), isInvA_pk pkX, isInvA_pk pkSs,
    Bool.and_true, Bool.and_true]
  exact c7044R

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
open scoped MatrixGroups Matrix LinearAlgebra.Projectivization in
theorem facts7044 :
    ruChainOK 26 psl26Strong 3 9 [0, 1, 2] psl26Words = true ∧
      rawOrbitSizes 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) = [26, 25, 12] ∧
      eqA 26 psl26Strong[0]! psl26X = true ∧ eqA 26 psl26Strong[1]! psl26S = true ∧
      eqA 26 psl26Strong[2]! psl26T = true ∧ psl26OrdersOK psl26Levels = true ∧
      psl26D.size = 26 ∧ eqA 26 psl26D[0]! (idA 26) = true ∧ psl26DClosed psl26X = true ∧
      psl26DClosed psl26S = true ∧ psl26DClosed (invCand 26 psl26X) = true ∧
      psl26DClosed (invCand 26 psl26S) = true ∧ (psl26D.all fun e => !eqA 26 e psl26T) = true ∧
      psl26RelOK = true ∧
      (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 0).pts.size = 26 ∧
      (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 1).pts.size = 25 ∧
      (ChainArrays.lev 26 psl26Strong (ruBaseArr 26 [0, 1, 2]) 2).pts.size = 12 := by
  have hw := c7044W
  obtain ⟨n0, n1, n2⟩ := cnt
  refine ⟨rawChainK_sound (NS := P26.NS) bindsP P26.head P26.hl
      (Nat.le_of_ble_eq_true (by quickRfl)) P26.hs, ?_, ?_, ?_, ?_, orders,
    (binds_of_check c7044D).1, ?_, closed pkX c7044L.1, closed pkSs c7044L.2.1,
    closed (pk_inv hw pkX) c7044L.2.2.1, closed (pk_inv hw pkSs) c7044L.2.2.2, avoidT, rel,
    ((levP (i := 0) (by norm_num)).1).trans n0, ((levP (i := 1) (by norm_num)).1).trans n1,
    ((levP (i := 2) (by norm_num)).1).trans n2⟩
  · rw [rawOrbitSizesK_sound bindsP c7044P P26.hl]
    simp [List.range_succ, n0, n1, n2]
  · rw [eqA_pk hw (pkS (by norm_num)) pkX]
    exact Nat.beq_refl _
  · rw [eqA_pk hw (pkS (by norm_num)) pkSs]
    exact Nat.beq_refl _
  · rw [eqA_pk hw (pkS (by norm_num)) pkT]
    exact Nat.beq_refl _
  · rw [eqA_pk hw (pkD (by norm_num)) (pk_id hw)]
    exact c7044A.2

end CertificateChecks.KernelPSL26

end
