module

public import Certificates.Kernel.SuzC17323.Checks
public import Certificates.Kernel.SuzThree13637.BindFacts
public import CFSG.Certificates.Kernel.K426KSound
public import CFSG.Certificates.Kernel.HeDihKSound
public import CFSG.Certificates.Kernel.D4Sound
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzC17323

open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.HeDih
open CFSG.KC.K426K CFSG.KC.BfsPin CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump
open CFSG.HardMathSupport.Dickson.I271.TabSuzC CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.KD.SuzThree13637
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CFSG.Monster.B.Co2 (allLt_iff)

theorem aN : AE.N = 360 := Nat.eq_of_beq_eq_true nE.1
theorem aNg : AE.ng = 2 := Nat.eq_of_beq_eq_true nE.2.1
theorem sN : SE.N = 9 := Nat.eq_of_beq_eq_true nE.2.2.1
theorem sNg : SE.ng = 2 := Nat.eq_of_beq_eq_true nE.2.2.2

theorem map_get {f : Array Nat → Array Nat} {a : Array (Array Nat)} {k : Nat} (hk : k < a.size) :
    (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), getElem!_pos a k hk, Array.getElem_map]

theorem aTSize : aTuples.size = 2 := rfl
theorem sTSize : sTuples.size = 2 := rfl

theorem aGet : ∀ k < 2, (aGens (levels ()))[k]! = unpack 1782 11 (AE.G k) := by
  intro k hk
  obtain ⟨h1, h2⟩ := rbA k hk
  have e : (aGens (levels ()))[k]! = rebuild (levels ()) aTuples[k]! := map_get (by
    rw [aTSize]; exact hk)
  rw [e, rebuild_eq h1, Nat.eq_of_beq_eq_true h2]

theorem sGet : ∀ k < 2, (sGens (levels ()))[k]! = unpack 1782 11 (SE.G k) := by
  intro k hk
  obtain ⟨h1, h2⟩ := rbS k hk
  have e : (sGens (levels ()))[k]! = rebuild (levels ()) sTuples[k]! := map_get (by
    rw [sTSize]; exact hk)
  rw [e, rebuild_eq h1, Nat.eq_of_beq_eq_true h2]

theorem yGet : yArr (levels ()) = unpack 1782 11 (CE.G 0) := by
  unfold yArr
  rw [rebuild_eq rbY.1, Nat.eq_of_beq_eq_true rbY.2]

theorem tGet : tArr (levels ()) = unpack 1782 11 TP := rebuild_eq rbT

theorem aSize : (aGens (levels ())).size = 2 := by
  unfold aGens
  rw [Array.size_map, aTSize]

theorem sSize : (sGens (levels ())).size = 2 := by
  unfold sGens
  rw [Array.size_map, sTSize]

theorem bindA : BindA 1782 11 (aGens (levels ())) AE.ng AE.G := by
  rw [aNg]
  exact ⟨aSize, aGet⟩

theorem bindS : BindA 1782 11 (sGens (levels ())) SE.ng SE.G := by
  rw [sNg]
  exact ⟨sSize, sGet⟩

theorem pA : ∀ k < AE.ng, permB 1782 11 (AE.G k) = true := fun k hk =>
  (pAS k (by rw [aNg] at hk; exact hk)).1

theorem pS : ∀ k < SE.ng, permB 1782 11 (SE.G k) = true := fun k hk =>
  (pAS k (by rw [sNg] at hk; exact hk)).2

theorem pC : ∀ k < CE.ng, permB 1782 11 (CE.G k) = true := fun k hk =>
  (ce_reb' (by rw [ce_n'.2] at hk; exact hk)).2.2

theorem keysEq : keys.toList = cKeys := rfl

theorem okA : bfsK 1782 11 AE.ng AE.G AE.N AE.T AE.E AE.S = true :=
  bfsK_of_slices (L := 120) (K := 3) (C := AE.C) (aN.trans (by norm_num)) (by norm_num) hw AE.g
    AE.csAll AE.t0 AE.dist (Nat.eq_of_beq_eq_true AE.c0) (Nat.eq_of_beq_eq_true AE.cK) AE.rsAll

theorem enumA : enumOK 1782 (aGens (levels ())) cKeys (aCert (levels ())) = true ∧
    (aCert (levels ())).pts.size = AE.N ∧
    ∀ i < AE.N, (aCert (levels ())).pts[i]! = unpack 1782 11 (AE.T i) := by
  have h := enum_of (fuel := 400) bindA pA okA (by decide) AE.keys
    (by rw [aN]; omega)
  rw [keysEq] at h
  exact h

theorem enumS : enumOK 1782 (sGens (levels ())) cKeys (sCert (levels ())) = true ∧
    (sCert (levels ())).pts.size = SE.N ∧
    ∀ i < SE.N, (sCert (levels ())).pts[i]! = unpack 1782 11 (SE.T i) := by
  have h := enum_of (fuel := 12) bindS pS SE.ok (by decide) SE.keys
    (by rw [sN]; omega)
  rw [keysEq] at h
  exact h

theorem pAT : ∀ i < AE.N, permB 1782 11 (AE.T i) = true := CFSG.KC.D4K.permB_pts okA pA

theorem memA {x : Nat} (h : memIdxK AE.N AE.T AE.S x = true) :
    (aCert (levels ())).pts.toList.any (eqA 1782 (unpack 1782 11 x)) = true :=
  any_of_memIdxK hw enumA.2.1 enumA.2.2 pAT h

theorem inP_of {G : Nat} (h : Nat.beq (Nat.shiftRight G (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) G t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G = true) :
    inP (levels ()) (unpack 1782 11 G) = true := by
  unfold inP CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.levels
  exact siftA_of Suz2306.binds Suz2306.perm SuzC.hl h

theorem c1 : derivedLeOK 1782 (cGens (levels ())) (aGens (levels ())) cKeys (aCert (levels ()))
    360 = true :=
  derivedLeOK_of hw enumA.1 enumA.2.1 enumA.2.2 pAT c_gen pC bindA pA aN derA

theorem c2 : allLt (aGens (levels ())).size (fun l => inP (levels ()) (aGens (levels ()))[l]! &&
    commA 1782 (aGens (levels ()))[l]! (yArr (levels ()))) = true := by
  rw [allLt_iff]
  intro l hl
  rw [aSize] at hl
  have hp := (pAS l hl).1
  have hy := pC 0 (by rw [ce_n'.2]; norm_num)
  rw [aGet l hl, yGet, inP_of (siftAG l hl)]
  unfold commA
  rw [comp_unpack' hw hp hy, comp_unpack' hw hy hp,
    eqA_unpack' hw (permB_pcomp hw hp hy) (permB_pcomp hw hy hp)]
  exact commY l hl

theorem c3 : wordsOneOK 1782 (aGens (levels ())) j3tLiftRels = true := by
  have hp : ∀ k < 2, PP 1782 11 (AE.G k) := fun k hk => pp_of_permB hw (pAS k hk).1
  unfold wordsOneOK
  rw [Bool.and_eq_true, allLt_iff, aSize, List.all_eq_true]
  refine ⟨fun k hk => by rw [aGet k hk]; exact validA_of (pAS k hk).1, fun wd hwd => ?_⟩
  obtain ⟨h1, h2⟩ := evalWA_unpack hw aGet hp wd
  rw [h1, idA_eq hw, eqA_PP h2 (PP.id hw)]
  exact List.all_eq_true.1 relA wd hwd

theorem c5 : allLt (sGens (levels ())).size
    (fun l => (aCert (levels ())).pts.toList.any (eqA 1782 (sGens (levels ()))[l]!)) = true := by
  rw [allLt_iff]
  intro l hl
  rw [sSize] at hl
  rw [sGet l hl]
  exact memA (Orb.allN_iff.1 memS l (by rw [sNg]; exact hl))

theorem c6 : commA 1782 (sGens (levels ()))[0]! (sGens (levels ()))[1]! = true := by
  have h0 := (pAS 0 (by norm_num)).2
  have h1 := (pAS 1 (by norm_num)).2
  rw [sGet 0 (by norm_num), sGet 1 (by norm_num)]
  unfold commA
  rw [comp_unpack' hw h0 h1, comp_unpack' hw h1 h0,
    eqA_unpack' hw (permB_pcomp hw h0 h1) (permB_pcomp hw h1 h0)]
  exact commS

theorem c7 : allLt (sGens (levels ())).size
    (fun l => eqA 1782 (powArr 1782 (sGens (levels ()))[l]! 3) (idA 1782)) = true := by
  rw [allLt_iff]
  intro l hl
  rw [sSize] at hl
  rw [sGet l hl, powEq_id hw (pAS l hl).2]
  exact cubeS l hl

theorem c8 : (validA 1782 (tArr (levels ())) && inP (levels ()) (tArr (levels ()))) = true := by
  rw [tGet, validA_of pT, inP_of siftT]
  rfl

theorem c9 : allLt (aGens (levels ())).size (fun l =>
    (aCert (levels ())).pts.toList.any (eqA 1782 (conjA 1782 (tArr (levels ()))
      (aGens (levels ()))[l]!)) &&
    (aCert (levels ())).pts.toList.any (eqA 1782 (conjInvA 1782 (tArr (levels ()))
      (aGens (levels ()))[l]!))) = true := by
  rw [allLt_iff]
  intro l hl
  rw [aSize] at hl
  have hp := (pAS l hl).1
  obtain ⟨h1, h2⟩ := conjTA l hl
  rw [aGet l hl, tGet, conj_unpack' hw pT hp, conjInv_unpack hw pT hp]
  have e1 := memA h1
  have e2 := memA h2
  unfold cj cm at e1
  unfold cm at e2
  rw [e1, e2]
  rfl

theorem c10 : eqA 1782 (conjA 1782 (tArr (levels ())) (sGens (levels ()))[0]!)
    (sGens (levels ()))[0]! = true := by
  have h0 := (pAS 0 (by norm_num)).2
  rw [sGet 0 (by norm_num), tGet, conj_unpack' hw pT h0,
    eqA_unpack' hw (permB_pcomp hw pT (permB_pcomp hw h0 (permB_pinvS hw pT))) h0]
  exact conjTS.1

theorem c11 : eqA 1782 (conjA 1782 (tArr (levels ())) (sGens (levels ()))[1]!)
    (powArr 1782 (sGens (levels ()))[1]! 2) = true := by
  have h1 := (pAS 1 (by norm_num)).2
  rw [sGet 1 (by norm_num), tGet, conj_unpack' hw pT h1, pow_unpack' hw h1,
    eqA_unpack' hw (permB_pcomp hw pT (permB_pcomp hw h1 (permB_pinvS hw pT)))
      (permB_ppow hw h1 2)]
  exact conjTS.2

theorem tabSuzC_ok : tabSuzCCheck () = true := by
  have c4 : (enumOK 1782 (sGens (levels ())) cKeys (sCert (levels ())) &&
      (sCert (levels ())).pts.size == 9) = true := by
    rw [enumS.1, enumS.2.1, sN]
    rfl
  unfold tabSuzCCheck
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, Bool.and_true, Bool.true_and,
    Bool.and_assoc]

end CertificateChecks.KernelSuzC17323

end
