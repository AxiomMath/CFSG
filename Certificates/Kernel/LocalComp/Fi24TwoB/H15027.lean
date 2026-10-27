module

public import Certificates.Kernel.LocalComp.Fi24TwoB.G15027
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CertificateChecks.KernelSpor.Fi24C
open CertificateChecks.KernelSpor CertificateChecks.KernelLC
open CFSG.ComponentClassification.RankTwoSporadic.Cert (regIndex inRegs powA prodA)
open CFSG.Sporadic.FischerOddCore (fi24T fi24KStrong)
open CFSG.RankThree.Native (enumOK enumBfs keyA validA)

theorem squares : ∀ i < 4096,
    eqA 504 (compA 504 fi24NCert.pts[i]! fi24NCert.pts[i]!) (idA 504) = true := by
  intro i hi
  have h := of_slices (L := 32) (K := 128)
    (f := fun i => strictB (Fi24BN.T i) fun t => Nat.beq (pcomp 504 9 (mask 9) t t) (pidn 504 9))
    (by norm_num) (fun s hs => Fi24BQ.sqAll s hs) i (by omega)
  simp only [strictB_app] at h
  rw [pt_get hi, compA_unpack (cnN hi) (cnN hi), idA_eq,
    eqA_unpack (canonK_pcomp (cnN hi) (cnN hi)) cnId]
  exact h

theorem sj_in : ∀ j < 378, inRegs 504 fi24NKey fi24NCert.pts (regIndex 504 fi24NKey fi24NCert.pts)
    fi24T[j]! = true := by
  intro j hj
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec Fi24BQ.kW j hj)
  rw [fi24T_get hj, ← Nat.eq_of_beq_eq_true h2]
  exact inRegs_pts (Nat.blt_eq.mp h1)

theorem gens_sift : ∀ k < 12,
    siftA 504 fi24KdLevels fi24KdBase.toArray 0 fi24NGens[k]! = true := by
  intro k hk
  have h : Fi24BQ.sg k = true := by
    rcases Nat.lt_or_ge k 6 with h6 | h6
    · exact allN_spec Fi24BQ.kSift0 k h6
    · have := allN_spec Fi24BQ.kSift1 (k - 6) (by omega)
      have e : Nat.add 6 (k - 6) = k := by
        rw [Nat.add_eq]
        omega
      rwa [e] at this
  unfold fi24KdLevels
  rw [dS, siftK_eq bindsD permD Fi24BKd.hl (gens_get hk) (hi_of (cnG hk))
    (range_of_canonK (cnG hk))]
  exact h

theorem reps_valid : ∀ o < 3, validA 504 fi24NOrbReps[o]! = true := by
  intro o ho
  interval_cases o
  · rw [reps_get.1]
    exact validA_unpack (cnR (by norm_num)).2
  · rw [reps_get.2.1]
    obtain ⟨X, hX⟩ := tree_facts.2.2 0 (by norm_num)
    exact CFSG.RankThree.Native.F2.validA_of_rep hX
  · rw [reps_get.2.2]
    exact validA_unpack (cnR (by norm_num)).2

theorem elts_ok : ∀ o < 3, ∀ j < ((fi24NOrbTrees.map fi24KdTreeElts)[o]!).size,
    validA 504 ((fi24NOrbTrees.map fi24KdTreeElts)[o]!)[j]! = true ∧
      siftA 504 fi24KdLevels fi24KdBase.toArray 0 ((fi24NOrbTrees.map fi24KdTreeElts)[o]!)[j]! =
        true := by
  intro o ho j hj
  rw [map_get (by simpa [fi24NOrbTrees] using ho)] at hj ⊢
  obtain ⟨g, hg, hr⟩ := elts_mem (trees_valid ho) j hj
  exact ⟨CFSG.RankThree.Native.F2.validA_of_rep hr, sift_of_mem hr hg⟩

theorem cover : ∀ i < 4096, (eqA 504 fi24NCert.pts[i]! (idA 504) ||
    inRegs 504 fi24NKey Tl[0]! (Tl.map (regIndex 504 fi24NKey))[0]! fi24NCert.pts[i]! ||
    inRegs 504 fi24NKey Tl[1]! (Tl.map (regIndex 504 fi24NKey))[1]! fi24NCert.pts[i]! ||
    inRegs 504 fi24NKey Tl[2]! (Tl.map (regIndex 504 fi24NKey))[2]! fi24NCert.pts[i]!) = true := by
  intro i hi
  have h := of_slices (L := 1024) (K := 4) (by norm_num) Fi24BQ.covAll i (by omega)
  unfold Fi24BQ.covK at h
  rw [strictB_app] at h
  rw [pt_get hi]
  cases e3 : Nat.beq (Fi24BQ.CO i) 3
  · rw [e3] at h
    change bAnd(Nat.blt (Fi24BQ.CO i) 3, bAnd(Nat.blt (Fi24BQ.CJ i) (Fi24BQ.NM (Fi24BQ.CO i)),
      Nat.beq (Fi24BX.X (Fi24BQ.CO i) (Fi24BQ.CJ i)) (Fi24BN.T i))) = true at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    have ho := Nat.blt_eq.mp h1
    have hj := Nat.blt_eq.mp h3
    rw [← Nat.eq_of_beq_eq_true h4]
    simp only [Bool.or_eq_true]
    generalize Fi24BQ.CO i = o at ho hj
    generalize Fi24BQ.CJ i = j at hj
    interval_cases o
    · exact Or.inl (Or.inl (Or.inr (inRegs_tl (by norm_num) hj)))
    · exact Or.inl (Or.inr (inRegs_tl (by norm_num) hj))
    · exact Or.inr (inRegs_tl (by norm_num) hj)
  · rw [e3] at h
    change Nat.beq (Fi24BN.T i) (pidn 504 9) = true at h
    rw [Nat.eq_of_beq_eq_true h, ← idA_eq, eqA_refl]
    rfl

theorem prod0 : fi24ProdOK Tl (Tl.map (regIndex 504 fi24NKey)) 0 0 58 340 = true := by
  have hk := Fi24BQ.kProd
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩ := hk
  have c0 := tl0.2
  unfold fi24ProdOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [tl0.1]
  refine ⟨⟨⟨by simp, by simp⟩, ?_⟩, ?_⟩
  · rw [getElem!_pos _ 0 (by simp), getElem!_pos _ 58 (by simp), Array.getElem_ofFn,
      Array.getElem_ofFn, fi24T_get (by norm_num)]
    change eqA 504 (compA 504 (unpack 504 9 (Fi24BX.X 0 0)) (unpack 504 9 (Fi24BX.X 0 58)))
      (unpack 504 9 (Fi24ST.T 340)) = true
    rw [compA_unpack (c0 0 (by norm_num)) (c0 58 (by norm_num)),
      eqA_unpack (canonK_pcomp (c0 0 (by norm_num)) (c0 58 (by norm_num))) (cnT (by norm_num))]
    exact h1
  · rw [fi24T_get (by norm_num), ← Nat.eq_of_beq_eq_true h3]
    exact inRegs_tl (by norm_num) (Nat.blt_eq.mp h2)

theorem prod2 : fi24ProdOK Tl (Tl.map (regIndex 504 fi24NKey)) 2 0 3 80 = true := by
  have hk := Fi24BQ.kProd
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, h1⟩, h2⟩, h3⟩ := hk
  have c2 := tl2.2
  unfold fi24ProdOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [tl2.1]
  refine ⟨⟨⟨by simp, by simp⟩, ?_⟩, ?_⟩
  · rw [getElem!_pos _ 0 (by simp), getElem!_pos _ 3 (by simp), Array.getElem_ofFn,
      Array.getElem_ofFn, fi24T_get (by norm_num)]
    change eqA 504 (compA 504 (unpack 504 9 (Fi24BX.X 2 0)) (unpack 504 9 (Fi24BX.X 2 3)))
      (unpack 504 9 (Fi24ST.T 80)) = true
    rw [compA_unpack (c2 0 (by norm_num)) (c2 3 (by norm_num)),
      eqA_unpack (canonK_pcomp (c2 0 (by norm_num)) (c2 3 (by norm_num))) (cnT (by norm_num))]
    exact h1
  · rw [fi24T_get (by norm_num), ← Nat.eq_of_beq_eq_true h3]
    exact inRegs_tl (by norm_num) (Nat.blt_eq.mp h2)

theorem gens_in : ∀ k < 12,
    inRegs 504 fi24NKey Tl[1]! (Tl.map (regIndex 504 fi24NKey))[1]! fi24NGens[k]! = true := by
  intro k hk
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec Fi24BQ.kWG k hk)
  rw [gens_get hk, ← Nat.eq_of_beq_eq_true h2]
  exact inRegs_tl (by norm_num) (Nat.blt_eq.mp h1)

theorem nOK : fi24NOK = true := by
  unfold fi24NOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨enum_ok, pts_size⟩, allLt_iff.2 squares⟩, allLt_iff.2 sj_in⟩,
    allLt_iff.2 gens_sift⟩, allLt_iff.2 fun o ho => ?_⟩, allLt_iff.2 cover⟩, prod0⟩, prod2⟩,
    allLt_iff.2 gens_in⟩
  simp only [Bool.and_eq_true]
  exact ⟨reps_valid o ho, allLt_iff.2 fun j hj => by
    simp only [Bool.and_eq_true]
    exact elts_ok o ho j hj⟩

theorem powA_unpack {p : Nat} (hp : Cn 504 9 p) : ∀ m : Nat,
    powA 504 (unpack 504 9 p) m = unpack 504 9 (Fi24BQ.powK p m) ∧ Cn 504 9 (Fi24BQ.powK p m)
  | 0 => ⟨idA_eq, cnId⟩
  | m + 1 => by
    obtain ⟨ih1, ih2⟩ := powA_unpack hp m
    have e : powA 504 (unpack 504 9 p) (m + 1) =
        compA 504 (unpack 504 9 p) (powA 504 (unpack 504 9 p) m) := by
      simp only [powA, prodA, List.replicate_succ, List.foldr_cons]
    rw [e, ih1, compA_unpack hp ih2]
    exact ⟨rfl, canonK_pcomp hp ih2⟩

theorem letters_ok : fi24QWords.all (fun e => e.1.all fun z => z == 1 || z == 2) = true := by
  decide

theorem qOK : fi24QOK = true := by
  unfold fi24QOK
  rw [List.all_eq_true]
  intro e he
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 he
  have hk13 : k < 13 := by simpa [fi24QWords] using hk
  have hL := List.all_eq_true.1 letters_ok _ he
  rw [Bool.and_eq_true]
  refine ⟨hL, ?_⟩
  have hw : Fi24BQ.wq k = true := by
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · exact allN_spec Fi24BQ.kQ0 k h4
    rcases Nat.lt_or_ge k 8 with h8 | h8
    · have := allN_spec Fi24BQ.kQ1 (k - 4) (by omega)
      have e4 : Nat.add 4 (k - 4) = k := by
        rw [Nat.add_eq]
        omega
      rwa [e4] at this
    · have := allN_spec Fi24BQ.kQ2 (k - 8) (by omega)
      have e8 : Nat.add 8 (k - 8) = k := by
        rw [Nat.add_eq]
        omega
      rwa [e8] at this
  unfold Fi24BQ.wq at hw
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hw
  rw [getElem!_pos fi24QWords k hk, hke] at h2
  obtain ⟨w1, w2⟩ := word_eq e.1
  rw [w1, (powA_unpack w2 _).1, ← Nat.eq_of_beq_eq_true h2]
  exact inRegs_pts (Nat.blt_eq.mp h1)

end CertificateChecks.KernelLC.Fi24B

end
