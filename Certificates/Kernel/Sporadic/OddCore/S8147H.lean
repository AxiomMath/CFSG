module

public import Certificates.Kernel.Sporadic.OddCore.S8147F

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KS.HNA CFSG.KC.PermTool CFSG.KS.EnumBase
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

theorem get_of_eq {a b : Array (Array Nat)} (h : a = b) {i : Nat} (hi : i < a.size) :
    a[i] = b[i]'(h ▸ hi) := by
  subst h
  rfl

theorem app_get {A L : Array (Array Nat)} {k : Nat} (hk : k < A.size) : (A ++ L)[k]! = A[k]! := by
  rw [getElem!_pos (A ++ L) k (by simp; omega), Array.getElem_append_left hk, getElem!_pos A k hk]

theorem bfs_gen5 {ms : Array (Array Nat)} {fuel : Nat} {z a0 a1 b0 b1 q : Array Nat}
    (hms : ms = #[a0, a1, b0, b1]) (hF : 2 ≤ fuel)
    (c0 : compA 1782 a0 z = a0) (c1 : compA 1782 a1 z = a1) (c2 : compA 1782 b0 z = b0)
    (c3 : compA 1782 b1 z = b1)
    (d1 : eqA 1782 z a0 = false) (d2 : eqA 1782 z a1 = false) (d3 : eqA 1782 a0 a1 = false)
    (d4 : eqA 1782 z b0 = false) (d5 : eqA 1782 a0 b0 = false) (d6 : eqA 1782 a1 b0 = false)
    (d7 : eqA 1782 z b1 = false) (d8 : eqA 1782 a0 b1 = false) (d9 : eqA 1782 a1 b1 = false)
    (d10 : eqA 1782 b0 b1 = false) (c5 : compA 1782 a0 a0 = q)
    (n5 : ∀ k < 5, eqA 1782 (#[z, a0, a1, b0, b1] : Array (Array Nat))[k]! q = false) :
    ∃ L : Array (Array Nat), (suzFiveBfsLoop ms fuel 0 (suzFiveAdd (#[], ∅) z)).1 =
      #[z, a0, a1, b0, b1, q] ++ L := by
  obtain ⟨F, rfl⟩ : ∃ F, fuel = F + 1 + 1 := ⟨fuel - 2, by omega⟩
  have g0 : Good (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) := good_add good_empty z
  have f0 : (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z).1 = #[z] := rfl
  rw [loop_succ ms (F + 1) 0 _ (by rw [f0]; simp)]
  have ez : (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z).1[0]'(by rw [f0]; simp) = z := by
    simp only [f0]
    rfl
  rw [ez]
  obtain ⟨v1, g1⟩ := visit1 (st := suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) g0 f0 c0 c1 c2 c3
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
  rw [hms]
  rw [loop_succ _ F 1 _ (by rw [v1]; simp)]
  rw [get_of_eq v1]
  change ∃ L, (suzFiveBfsLoop #[a0, a1, b0, b1] F (1 + 1)
    (suzFiveVisit #[a0, a1, b0, b1] (suzFiveVisit #[a0, a1, b0, b1]
      (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) z) a0)).1 = _
  generalize hS : suzFiveVisit #[a0, a1, b0, b1] (suzFiveAdd ((#[], ∅) : SuzFiveBfsState) z) z = S
    at v1 g1
  rw [visit_lit]
  have e1 : stepF a0 S a0 = suzFiveAdd S q := by
    rw [stepF_new g1, c5]
    intro k hk
    rw [v1] at hk
    rw [v1, c5]
    exact n5 k (by simpa using hk)
  rw [e1]
  obtain ⟨L1, e2⟩ := stepF_prefix a0 (suzFiveAdd S q) a1
  obtain ⟨L2, e3⟩ := stepF_prefix a0 (stepF a0 (suzFiveAdd S q) a1) b0
  obtain ⟨L3, e4⟩ := stepF_prefix a0 (stepF a0 (stepF a0 (suzFiveAdd S q) a1) b0) b1
  obtain ⟨L4, e5⟩ := loop_prefix #[a0, a1, b0, b1] F (1 + 1)
    (stepF a0 (stepF a0 (stepF a0 (suzFiveAdd S q) a1) b0) b1)
  refine ⟨L1 ++ L2 ++ L3 ++ L4, ?_⟩
  rw [e5, e4, e3, e2, add_fst, v1]
  simp only [Array.append_assoc]
  rfl

theorem lit_get {z a0 a1 b0 b1 : Array Nat} {L : Array (Array Nat)} :
    (#[z, a0, a1, b0, b1] ++ L)[1]! = a0 ∧ (#[z, a0, a1, b0, b1] ++ L)[2]! = a1 ∧
      (#[z, a0, a1, b0, b1] ++ L)[3]! = b0 ∧ (#[z, a0, a1, b0, b1] ++ L)[4]! = b1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [app_get (by simp)] <;> rfl

theorem lit_get5 {z a0 a1 b0 b1 q : Array Nat} {L : Array (Array Nat)} :
    (#[z, a0, a1, b0, b1, q] ++ L)[5]! = q := by
  rw [app_get (by simp)]
  rfl

theorem n5_of {z a0 a1 b0 b1 q : Array Nat} (h0 : eqA 1782 z q = false)
    (h1 : eqA 1782 a0 q = false) (h2 : eqA 1782 a1 q = false) (h3 : eqA 1782 b0 q = false)
    (h4 : eqA 1782 b1 q = false) :
    ∀ k < 5, eqA 1782 (#[z, a0, a1, b0, b1] : Array (Array Nat))[k]! q = false := by
  intro k hk
  interval_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem fact_ge : 2 ≤ Nat.factorial 1782 := by
  have := Nat.self_le_factorial 1782
  omega

theorem bfs_eq (i : Nat) : suzFiveBfs i =
    (suzFiveBfsLoop (suzFiveMults i) (Nat.factorial 1782) 0 (suzFiveAdd (#[], ∅) (idA 1782))).1 := rfl

theorem bfs_get {i G0 G1 : Nat}
    (hc : suzFiveCArrs i = #[unpack 1782 11 G0, unpack 1782 11 G1]) (hP0 : PP 1782 11 G0)
    (hP1 : PP 1782 11 G1) (hpre : preChk G0 G1 = true) :
    (suzFiveBfs i)[1]! = unpack 1782 11 G0 ∧ (suzFiveBfs i)[2]! = unpack 1782 11 G1 ∧
      (suzFiveBfs i)[3]! = unpack 1782 11 (pinvS 1782 11 (mask 11) G0) ∧
      (suzFiveBfs i)[4]! = unpack 1782 11 (pinvS 1782 11 (mask 11) G1) := by
  obtain ⟨z0, z1, z2, z3, h01, h0i0, h0i1, h1i0, h1i1, hi0i1⟩ := preChk_spec hpre
  have hZ := PP.id (n := 1782) (w := 11) szk
  obtain ⟨L, e⟩ := bfs_gen (z := unpack 1782 11 (pidn 1782 11)) (mults_eq hc hP0 hP1 hpre) fact_ge
    (by rw [cmpU hP0 hZ, pcomp_id hP0]) (by rw [cmpU hP1 hZ, pcomp_id hP1])
    (by rw [cmpU hP0.inv hZ, pcomp_id hP0.inv]) (by rw [cmpU hP1.inv hZ, pcomp_id hP1.inv])
    (eqA_ne hZ hP0 z0) (eqA_ne hZ hP1 z1) (eqA_ne hP0 hP1 h01) (eqA_ne hZ hP0.inv z2)
    (eqA_ne hP0 hP0.inv h0i0) (eqA_ne hP1 hP0.inv h1i0) (eqA_ne hZ hP1.inv z3)
    (eqA_ne hP0 hP1.inv h0i1) (eqA_ne hP1 hP1.inv h1i1) (eqA_ne hP0.inv hP1.inv hi0i1)
  rw [bfs_eq, idU, e]
  exact lit_get

theorem bfs_get5 {i G0 G1 : Nat}
    (hc : suzFiveCArrs i = #[unpack 1782 11 G0, unpack 1782 11 G1]) (hP0 : PP 1782 11 G0)
    (hP1 : PP 1782 11 G1) (hpre : preChk G0 G1 = true)
    (hq : Nat.beq (pcomp 1782 11 (mask 11) G0 G0) (pidn 1782 11) = false ∧
      Nat.beq (pcomp 1782 11 (mask 11) G0 G0) G0 = false ∧
      Nat.beq (pcomp 1782 11 (mask 11) G0 G0) G1 = false ∧
      Nat.beq (pcomp 1782 11 (mask 11) G0 G0) (pinvS 1782 11 (mask 11) G0) = false ∧
      Nat.beq (pcomp 1782 11 (mask 11) G0 G0) (pinvS 1782 11 (mask 11) G1) = false) :
    (suzFiveBfs i)[5]! = unpack 1782 11 (pcomp 1782 11 (mask 11) G0 G0) := by
  obtain ⟨z0, z1, z2, z3, h01, h0i0, h0i1, h1i0, h1i1, hi0i1⟩ := preChk_spec hpre
  obtain ⟨q0, q1, q2, q3, q4⟩ := hq
  have hZ := PP.id (n := 1782) (w := 11) szk
  have hQ := hP0.mul hP0
  obtain ⟨L, e⟩ := bfs_gen5 (z := unpack 1782 11 (pidn 1782 11))
    (q := unpack 1782 11 (pcomp 1782 11 (mask 11) G0 G0)) (mults_eq hc hP0 hP1 hpre) fact_ge
    (by rw [cmpU hP0 hZ, pcomp_id hP0]) (by rw [cmpU hP1 hZ, pcomp_id hP1])
    (by rw [cmpU hP0.inv hZ, pcomp_id hP0.inv]) (by rw [cmpU hP1.inv hZ, pcomp_id hP1.inv])
    (eqA_ne hZ hP0 z0) (eqA_ne hZ hP1 z1) (eqA_ne hP0 hP1 h01) (eqA_ne hZ hP0.inv z2)
    (eqA_ne hP0 hP0.inv h0i0) (eqA_ne hP1 hP0.inv h1i0) (eqA_ne hZ hP1.inv z3)
    (eqA_ne hP0 hP1.inv h0i1) (eqA_ne hP1 hP1.inv h1i1) (eqA_ne hP0.inv hP1.inv hi0i1)
    (cmpU hP0 hP0) (n5_of (eqA_ne hZ hQ (beq_comm' q0)) (eqA_ne hP0 hQ (beq_comm' q1))
      (eqA_ne hP1 hQ (beq_comm' q2)) (eqA_ne hP0.inv hQ (beq_comm' q3))
      (eqA_ne hP1.inv hQ (beq_comm' q4)))
  rw [bfs_eq, idU, e]
  exact lit_get5

theorem pairs_of {i N : Nat} {TC : Nat → Nat} (hi : i < 6)
    (hC : enumOK 1782 (suzFiveCArrs i) suzFiveKeys (suzFiveCCert i) = true ∧
      (suzFiveCCert i).pts.size = N ∧
      (∀ j < N, (suzFiveCCert i).pts[j]! = unpack 1782 11 (TC j)) ∧ ∀ j < N, PP 1782 11 (TC j))
    (hpl : ∀ l < suzFiveDerivedPairs[i]!.size, (suzFiveDerivedPairs[i]!)[l]!.1 < 2 ∧
      ∃ Y, PP 1782 11 Y ∧ (suzFiveBfs i)[(suzFiveDerivedPairs[i]!)[l]!.2]! = unpack 1782 11 Y ∧
        memK N TC Y = true) :
    suzFivePairsCheck i = true := by
  obtain ⟨-, c2, c3, c4⟩ := hC
  unfold suzFivePairsCheck
  simp only []
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro l hl
  obtain ⟨h1, Y, hY, hE, hm⟩ := hpl l hl
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, cArrs_size hi, hE]
  exact ⟨⟨h1, validU hY⟩, memK_any c2 c3 c4 hY hm⟩

theorem inL_iff {L : List Nat} {y : Nat} : inL L y = true ↔ y ∈ L := by
  induction L with
  | nil => simp [inL]
  | cons x L ih =>
    change bIf(Nat.beq x y, true, inL L y) = true ↔ _
    rw [bIf_eq, List.mem_cons]
    by_cases h : x = y
    · subst h
      simp
    · have hb : Nat.beq x y = false := by rw [beq_eq]; simpa using h
      rw [hb, if_neg Bool.false_ne_true, ih]
      constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm h
        · exact e

theorem orbit_of {i nd N L K : Nat} {Ls : List Nat} {DG G T E S C : Nat → Nat}
    (hLs : suzFiveOrbits[i]! = Ls) (hlt : ∀ x ∈ Ls, x < 1782) (hw : Ls.length + 1 < 2 ^ 3)
    (hds : (suzFiveDArrs i).size = nd) (hdg : ∀ l < nd, (suzFiveDArrs i)[l]! = unpack 1782 11 (DG l))
    (hDP : ∀ l < nd, PP 1782 11 (DG l)) (ho : oChk Ls nd DG G = true) (hNL : N = L * K)
    (hL : 0 < L)
    (hh : (szOK Ls.length 3 && allN nd (fun k => canonK Ls.length 3 (mask 3) (Nat.mul Ls.length 3)
      (G k)) && Nat.beq (T 0) (pidn Ls.length 3) && Nat.beq (C 0) 1 && Nat.beq (C K) N) = true)
    (hd : distinctK N T S = true)
    (hp : allN nd (fun k => permOK Ls.length 3 (mask 3) (Ls.length * 3) (G k)
      (pinvS Ls.length 3 (mask 3) (G k))) = true)
    (hsl : ∀ s < K, bAnd(canonSl Ls.length 3 T L s, runSl Ls.length 3 nd G T E L C s) = true)
    (hf : N ≤ 400) :
    suzFiveOrbitCheck (suzFiveDArrs i) suzFiveOrbits[i]! suzFiveOrbits[i]!.length N
      (suzFiveOrbitCert i) = true := by
  have hgs : ((suzFiveDArrs i).map (restrictArr Ls)).size = nd := by rw [Array.size_map, hds]
  have hgg : ∀ l < nd, ((suzFiveDArrs i).map (restrictArr Ls))[l]! = unpack Ls.length 3 (G l) := by
    intro l hl
    have ho' := allN_spec ho l hl
    rw [bAnd_eq, Bool.and_eq_true] at ho'
    rw [getElem!_pos _ l (by rw [hgs]; exact hl), Array.getElem_map,
      ← getElem!_pos (suzFiveDArrs i) l (by rw [hds]; exact hl), hdg l hl,
      restrictArr_unpack (hDP l hl).1 hlt hw, Nat.eq_of_beq_eq_true ho'.2]
  obtain ⟨e1, e2⟩ := enumO (m := Ls.length) hgs hgg hNL hL hh hd hp hsl hf
  unfold suzFiveOrbitCheck suzFiveOrbitCert
  rw [hLs]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨trivial, ?_⟩, e1⟩, e2⟩
  rw [Array.all_eq_true]
  intro l hl
  rw [hds] at hl
  have ho' := allN_spec ho l hl
  rw [bAnd_eq, Bool.and_eq_true] at ho'
  rw [List.all_eq_true]
  intro x hx
  rw [← getElem!_pos (suzFiveDArrs i) l (by rw [hds]; exact hl), hdg l hl, upk_get (hlt x hx),
    List.contains_iff_mem, ← inL_iff]
  exact (allL_iff.1 ho'.1) x hx

end CertificateChecks.KernelSpor.S8147

end
