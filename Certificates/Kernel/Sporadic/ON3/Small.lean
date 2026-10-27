
module

public import Certificates.Kernel.Sporadic.ON3.Strong
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KS.PW
open CFSG.Sporadic.ON.Native (nPts)

@[expose] def rposK (y : Nat) : Nat :=
  (List.range 32).foldr (fun t acc => if Data.TPoints[t]! == y then t else acc) 32

@[expose] def bposK (y : Nat) : Nat :=
  (List.range 240).foldr (fun u acc => if bpt Data.quotientBlocks u == y then u / 2 else acc) 120

theorem allBelowN_iff {n : Nat} {p : Nat → Bool} : allBelowN n p = true ↔ ∀ i < n, p i = true := by
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

theorem all_range {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true) :
    ∀ i < n, p i = true := fun i hi => List.all_eq_true.1 h i (List.mem_range.2 hi)

theorem r_points : ((List.range 32).all fun i => decide (Data.TPoints[i]! < 245520) &&
    (List.range i).all fun j => Data.TPoints[j]! != Data.TPoints[i]!) = true := by
  decide +kernel

theorem b_points : (Data.quotientBlocks.size == 120 &&
    ((List.range 120).all fun i => Data.quotientBlocks[i]!.size == 2) &&
    (List.range 240).all fun u => decide (bpt Data.quotientBlocks u < 245520) &&
      (List.range u).all fun v => bpt Data.quotientBlocks v != bpt Data.quotientBlocks u) = true := by
  decide +kernel

theorem rpos_spec : rPos.size = 245520 ∧ ∀ i < 32, rPos[Data.TPoints[i]!]! = i := by
  have h := all_range r_points
  have hR : ∀ i < Data.TPoints.size, Data.TPoints[i]! < 245520 := fun i hi => by
    have := h i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  have hd : ∀ i < Data.TPoints.size, ∀ j < i, Data.TPoints[j]! ≠ Data.TPoints[i]! := by
    intro i hi j hj
    have := h i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have h' := all_range this.2 j hj
    simpa using h'
  exact posArr_spec hR hd

theorem bpos_spec : bPos.size = 245520 ∧ ∀ u < 240,
    bPos[bpt Data.quotientBlocks u]! = u / 2 := by
  have h := b_points
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, h2⟩, h3⟩ := h
  have hs' : 2 * Data.quotientBlocks.size = 240 := by rw [hs]
  refine blockPos_spec (fun i hi => ?_) (fun u hu => ?_) (fun u hu v hv => ?_)
  · have := all_range h2 i (by omega)
    simpa using this
  · have := all_range h3 u (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := all_range h3 u (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have h' := all_range this.2 v hv
    simpa using h'

theorem rtab_eq {g : Array Nat} {G : Nat → Nat}
    (hg : ∀ y < 245520, g[y]! = G y)
    (hok : ∀ k < 32, rposK (G Data.TPoints[k]!) < 32 ∧
      Data.TPoints[rposK (G Data.TPoints[k]!)]! = G Data.TPoints[k]!) :
    rTab g = Array.ofFn (n := 32) fun k => rposK (G Data.TPoints[k.val]!) := by
  have hR := all_range r_points
  have hP := rpos_spec.2
  have hsz : Data.TPoints.size = 32 := rfl
  unfold rTab restrictTab
  generalize rPos = P at hP
  refine arr_ext (F := fun k => rposK (G Data.TPoints[k]!)) (by rw [Array.size_map, hsz])
    fun k hk => ?_
  have hlt : Data.TPoints[k]! < 245520 := by
    have := hR k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  rw [getElem!_pos (Data.TPoints.map _) k (by rw [Array.size_map, hsz]; exact hk), Array.getElem_map,
    ← getElem!_pos Data.TPoints k (by rw [hsz]; exact hk), hg _ hlt]
  obtain ⟨t1, t2⟩ := hok k hk
  conv_lhs => rw [← t2]
  exact hP _ t1

theorem restrict_of {g : Array Nat} {G : Nat → Nat}
    (hg : ∀ y < 245520, g[y]! = G y)
    (hok : ∀ k < 32, rposK (G Data.TPoints[k]!) < 32 ∧
      Data.TPoints[rposK (G Data.TPoints[k]!)]! = G Data.TPoints[k]!) :
    restrictOK g Data.TPoints (rTab g) = true := by
  have hR := all_range r_points
  rw [rtab_eq hg hok]
  unfold restrictOK
  refine allBelowN_iff.2 fun k hk => ?_
  have hk' : k < 32 := hk
  have hlt : Data.TPoints[k]! < 245520 := by
    have := hR k hk'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  rw [ofFn_get' (f := fun k => rposK (G Data.TPoints[k]!)) hk', hg _ hlt]
  obtain ⟨t1, t2⟩ := hok k hk'
  have hsz : Data.TPoints.size = 32 := rfl
  rw [t2]
  simp [hsz, t1]

theorem btab_eq {g : Array Nat} {G : Nat → Nat}
    (hg : ∀ y < 245520, g[y]! = G y)
    (hok : ∀ i < 120, bposK (G (Data.quotientBlocks[i]!)[0]!) < 120 ∧
      inBlock Data.quotientBlocks[bposK (G (Data.quotientBlocks[i]!)[0]!)]!
        (G (Data.quotientBlocks[i]!)[0]!) = true) :
    bTab g = Array.ofFn (n := 120) fun i => bposK (G (Data.quotientBlocks[i.val]!)[0]!) := by
  have hb := b_points
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨hs, -⟩, h3⟩ := hb
  have hP := bpos_spec.2
  unfold bTab blockTab
  generalize bPos = P at hP
  refine arr_ext (F := fun i => bposK (G (Data.quotientBlocks[i]!)[0]!)) (by rw [Array.size_map, hs])
    fun i hi => ?_
  have hlt : (Data.quotientBlocks[i]!)[0]! < 245520 := by
    have := all_range h3 (2 * i) (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have e : bpt Data.quotientBlocks (2 * i) = (Data.quotientBlocks[i]!)[0]! := by
      unfold bpt
      rw [Nat.mul_div_cancel_left i (by norm_num : 0 < 2), Nat.mul_mod_right]
    rw [← e]
    exact this.1
  rw [getElem!_pos (Data.quotientBlocks.map _) i (by rw [Array.size_map, hs]; exact hi),
    Array.getElem_map, ← getElem!_pos Data.quotientBlocks i (by rw [hs]; exact hi), hg _ hlt]
  obtain ⟨t1, t2⟩ := hok i hi
  generalize G (Data.quotientBlocks[i]!)[0]! = y at t1 t2 ⊢
  unfold inBlock at t2
  simp only [Bool.or_eq_true, beq_iff_eq] at t2
  rcases t2 with e | e
  · have e' : bpt Data.quotientBlocks (2 * bposK y) = y := by
      unfold bpt
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_mod_right]
      exact e
    conv_lhs => rw [← e']
    rw [hP _ (by omega)]
    omega
  · have e' : bpt Data.quotientBlocks (2 * bposK y + 1) = y := by
      unfold bpt
      have d1 : (2 * bposK y + 1) / 2 = bposK y := by omega
      have d2 : (2 * bposK y + 1) % 2 = 1 := by omega
      rw [d1, d2]
      exact e
    conv_lhs => rw [← e']
    rw [hP _ (by omega)]
    omega

theorem bpt_eq {B : Array (Array Nat)} {i e : Nat} (he : e < 2) :
    bpt B (2 * i + e) = (B[i]!)[e]! := by
  unfold bpt
  have d1 : (2 * i + e) / 2 = i := by omega
  have d2 : (2 * i + e) % 2 = e := by omega
  rw [d1, d2]

theorem bpt_lt {i e : Nat} (hi : i < 120) (he : e < 2) : (Data.quotientBlocks[i]!)[e]! < 245520 := by
  have hb := b_points
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  have := all_range hb.2 (2 * i + e) (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rw [← bpt_eq he]
  exact this.1

@[expose] def blkK (G : Nat → Nat) (t : Nat → Nat) : Bool :=
  (List.range 120).all fun i => decide (t i < 120) &&
    inBlock Data.quotientBlocks[t i]! (G (Data.quotientBlocks[i]!)[0]!) &&
    inBlock Data.quotientBlocks[t i]! (G (Data.quotientBlocks[i]!)[1]!)

theorem blockImg_of {g : Array Nat} {G : Nat → Nat} {t : Array Nat}
    (hg : ∀ y < 245520, g[y]! = G y) (hk : blkK G (fun i => t[i]!) = true) :
    blockImgOK g Data.quotientBlocks t = true := by
  have hs : Data.quotientBlocks.size = 120 := rfl
  unfold blockImgOK
  refine allBelowN_iff.2 fun i hi => ?_
  rw [hs] at hi
  rw [hg _ (bpt_lt hi (by norm_num)), hg _ (bpt_lt hi (by norm_num))]
  exact all_range hk i hi

theorem blockTab_of {g : Array Nat} {G : Nat → Nat} (hg : ∀ y < 245520, g[y]! = G y)
    (hk : blkK G (fun i => bposK (G (Data.quotientBlocks[i]!)[0]!)) = true) :
    blockImgOK g Data.quotientBlocks (bTab g) = true ∧
      bTab g = Array.ofFn (n := 120) fun i => bposK (G (Data.quotientBlocks[i.val]!)[0]!) := by
  have e := btab_eq hg fun i hi => by
    have := all_range hk i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2⟩
  refine ⟨blockImg_of hg ?_, e⟩
  rw [e]
  unfold blkK at hk ⊢
  refine List.all_eq_true.2 fun i hi => ?_
  have hi' : i < 120 := List.mem_range.1 hi
  beta_reduce
  rw [ofFn_get' (f := fun i => bposK (G (Data.quotientBlocks[i]!)[0]!)) hi']
  exact List.all_eq_true.1 hk i hi

@[expose] noncomputable def peqK (n : Nat) (t u : Array Nat) : Bool :=
  CFSG.KC.Enum.allN n fun i => Nat.beq t[i]! u[i]!

@[expose] noncomputable def anyN (m : Nat) (q : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun j ih => bIf(q j, true, ih)) m

@[expose] noncomputable def coversK (n : Nat) (A B : Array (Array Nat)) : Bool :=
  CFSG.KC.Enum.allN A.size fun i =>
    bIf(peqK n A[i]! (pid n), true, anyN B.size fun j => peqK n A[i]! B[j]!)

theorem anyN_spec {q : Nat → Bool} : ∀ {m : Nat}, anyN m q = true → ∃ j < m, q j = true
  | 0, h => absurd h (by simp [anyN])
  | m + 1, h => by
    have h' : bIf(q m, true, anyN m q) = true := h
    cases hq : q m
    · rw [hq] at h'
      obtain ⟨j, hj, e⟩ := anyN_spec h'
      exact ⟨j, by omega, e⟩
    · exact ⟨m, by omega, hq⟩

theorem peq_of_K {n : Nat} {t u : Array Nat} (h : peqK n t u = true) : peq n t u = true := by
  unfold peq
  refine allBelowN_iff.2 fun i hi => ?_
  have := CFSG.KS.allN_spec h i hi
  simpa using this

theorem coversOK_of_K {n : Nat} {A B : Array (Array Nat)} (h : coversK n A B = true) :
    coversOK n A B = true := by
  unfold coversOK
  refine allBelowN_iff.2 fun i hi => ?_
  have h' := CFSG.KS.allN_spec h i hi
  cases hp : peqK n A[i]! (pid n)
  · rw [hp] at h'
    obtain ⟨j, hj, e⟩ := anyN_spec h'
    have hq := peq_of_K e
    rw [Bool.or_eq_true]
    right
    rw [Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro ha
    have := allBelowN_iff.1 ha j hj
    rw [hq] at this
    exact absurd this (by decide)
  · rw [peq_of_K hp]
    rfl

theorem tw_get {j : Nat} (hj : j < 6) :
    ∀ y < 245520, ((wordArrs Data.TWords)[j]!)[y]! = tG j y := by
  intro y hy
  rw [wordArrs_get (Nat.lt_of_lt_of_eq hj rfl), tG_eq hj]
  interval_cases j
  · exact (wordArr_get (let7 (k := 11) (by norm_num)) hy).1
  · exact (wordArr_get (let7 (k := 12) (by norm_num)) hy).1
  · exact (wordArr_get (let7 (k := 13) (by norm_num)) hy).1
  · exact (wordArr_get (let7 (k := 14) (by norm_num)) hy).1
  · exact (wordArr_get (let7 (k := 15) (by norm_num)) hy).1
  · exact (wordArr_get (let7 (k := 16) (by norm_num)) hy).1

@[expose] noncomputable def rArr : Array (Array Nat) :=
  Array.ofFn (n := 6) fun j => Array.ofFn (n := 32) fun k => rposK (tG j.val Data.TPoints[k.val]!)

theorem r_kernel : ((List.range 6).all fun j => (List.range 32).all fun k =>
      decide (rposK (tG j Data.TPoints[k]!) < 32) &&
        Data.TPoints[rposK (tG j Data.TPoints[k]!)]! == tG j Data.TPoints[k]!) &&
    ((List.range 32).all fun k => decide (Data.T32z[k]! < 32) &&
      Data.TPoints[Data.T32z[k]!]! == ZT Data.TPoints[k]!) &&
    coversK 32 rArr Data.T32Chain.generators && coversK 32 Data.T32Chain.generators rArr = true := by
  quickRfl

theorem map_eq' {f : Array Nat → Array Nat} {ws : Array (List Int)} {m : Nat}
    {T : Array (Array Nat)} (hs : (wordArrs ws).size = m) (hT : T.size = m)
    (h : ∀ j < m, f (wordArrs ws)[j]! = T[j]!) : (wordArrs ws).map f = T := by
  apply Array.ext
  · rw [Array.size_map, hs, hT]
  · intro j h1 h2
    have hj : j < m := by rw [hT] at h2; exact h2
    rw [Array.getElem_map, ← getElem!_pos (wordArrs ws) j (by rw [hs]; exact hj), h j hj,
      getElem!_pos T j h2]

theorem r_map : (wordArrs Data.TWords).map rTab = rArr := by
  have hk := r_kernel
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := hk
  refine map_eq' twords_size (by simp [rArr]) fun j hj => ?_
  unfold rArr
  rw [CertificateChecks.KernelSpor.ON.ofFn_get hj]
  refine rtab_eq (tw_get hj) fun k hk => ?_
  have := all_range (all_range h1 j hj) k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact this

theorem r_facts : pointsOK nPts Data.TPoints rPos = true ∧
    allBelowN 6 (fun j => restrictOK (wordArrs Data.TWords)[j]! Data.TPoints
      (rTab (wordArrs Data.TWords)[j]!)) = true ∧
    restrictOK zArr Data.TPoints Data.T32z = true ∧
    coversOK 32 ((wordArrs Data.TWords).map rTab) Data.T32Chain.generators = true ∧
    coversOK 32 Data.T32Chain.generators ((wordArrs Data.TWords).map rTab) = true := by
  have hk := r_kernel
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hk
  have hR := all_range r_points
  have hlt : ∀ k < 32, Data.TPoints[k]! < 245520 := fun k hk => by
    have := hR k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  refine ⟨?_, allBelowN_iff.2 fun j hj => restrict_of (tw_get hj) fun k hk => ?_, ?_,
    by rw [r_map]; exact coversOK_of_K h3, by rw [r_map]; exact coversOK_of_K h4⟩
  · unfold pointsOK
    rw [rpos_spec.1]
    simp only [beq_self_eq_true, Bool.true_and]
    refine allBelowN_iff.2 fun k hk => ?_
    have hk' : k < 32 := hk
    simp [hlt k hk', rpos_spec.2 k hk']
  · have := all_range (all_range h1 j hj) k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this
  · unfold restrictOK
    refine allBelowN_iff.2 fun k hk => ?_
    have hk' : k < 32 := hk
    rw [(z_get _ (hlt k hk')).1]
    exact all_range h2 k hk'

@[expose] noncomputable def bM : Array (Array Nat) :=
  Array.ofFn (n := 3) fun j => Array.ofFn (n := 120) fun i =>
    bposK (mG j.val (Data.quotientBlocks[i.val]!)[0]!)

@[expose] noncomputable def bL : Array (Array Nat) :=
  Array.ofFn (n := 2) fun j => Array.ofFn (n := 120) fun i =>
    bposK (lG j.val (Data.quotientBlocks[i.val]!)[0]!)

theorem b_kernel : ((List.range 3).all fun j =>
      blkK (mG j) fun i => bposK (mG j (Data.quotientBlocks[i]!)[0]!)) &&
    ((List.range 2).all fun j => blkK (lG j) fun i => bposK (lG j (Data.quotientBlocks[i]!)[0]!)) &&
    blkK QT (fun i => (pid 120)[i]!) &&
    coversK 120 bM Data.M120Chain.generators && coversK 120 Data.M120Chain.generators bM &&
    coversK 120 bL Data.L120Chain.generators && coversK 120 Data.L120Chain.generators bL =
      true := by
  quickRfl

theorem b_parts : (∀ j < 3, blockImgOK (wordArrs Data.MWords)[j]! Data.quotientBlocks
      (bTab (wordArrs Data.MWords)[j]!) = true ∧ bTab (wordArrs Data.MWords)[j]! = bM[j]!) ∧
    (∀ j < 2, blockImgOK (wordArrs Data.LWords)[j]! Data.quotientBlocks
      (bTab (wordArrs Data.LWords)[j]!) = true ∧ bTab (wordArrs Data.LWords)[j]! = bL[j]!) := by
  have hk := b_kernel
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hk
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨a, b⟩ := blockTab_of (fun y hy => (m_get hj y hy).1) (all_range h1 j hj)
    refine ⟨a, ?_⟩
    rw [b]
    unfold bM
    rw [CertificateChecks.KernelSpor.ON.ofFn_get hj]
  · obtain ⟨a, b⟩ := blockTab_of (fun y hy => (l_get hj y hy).1) (all_range h2 j hj)
    refine ⟨a, ?_⟩
    rw [b]
    unfold bL
    rw [CertificateChecks.KernelSpor.ON.ofFn_get hj]

theorem block_facts : blocksOK nPts Data.quotientBlocks bPos = true ∧
    allBelowN 3 (fun j => blockImgOK (wordArrs Data.MWords)[j]! Data.quotientBlocks
      (bTab (wordArrs Data.MWords)[j]!)) = true ∧
    allBelowN 2 (fun j => blockImgOK (wordArrs Data.LWords)[j]! Data.quotientBlocks
      (bTab (wordArrs Data.LWords)[j]!)) = true ∧
    coversOK 120 ((wordArrs Data.MWords).map bTab) Data.M120Chain.generators = true ∧
    coversOK 120 Data.M120Chain.generators ((wordArrs Data.MWords).map bTab) = true ∧
    coversOK 120 ((wordArrs Data.LWords).map bTab) Data.L120Chain.generators = true ∧
    coversOK 120 Data.L120Chain.generators ((wordArrs Data.LWords).map bTab) = true ∧
    blockImgOK qArr Data.quotientBlocks (pid 120) = true := by
  have hk := b_kernel
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hk
  obtain ⟨hM, hL⟩ := b_parts
  have eM : (wordArrs Data.MWords).map bTab = bM :=
    map_eq' (by rw [wordArrs, pwords_eq, Array.size_map]; rfl) (by simp [bM]) fun j hj => (hM j hj).2
  have eL : (wordArrs Data.LWords).map bTab = bL :=
    map_eq' (by rw [wordArrs, pwords_eq, Array.size_map]; rfl) (by simp [bL]) fun j hj => (hL j hj).2
  have hb := b_points
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨hs, h2⟩, hpt⟩ := hb
  refine ⟨?_, allBelowN_iff.2 fun j hj => (hM j hj).1, allBelowN_iff.2 fun j hj => (hL j hj).1,
    by rw [eM]; exact coversOK_of_K h4, by rw [eM]; exact coversOK_of_K h5,
    by rw [eL]; exact coversOK_of_K h6, by rw [eL]; exact coversOK_of_K h7,
    blockImg_of (fun y hy => (q_get y hy).1) h3⟩
  unfold blocksOK
  rw [bpos_spec.1]
  simp only [beq_self_eq_true, Bool.true_and]
  refine allBelowN_iff.2 fun i hi => ?_
  rw [hs] at hi
  have e0 : bpt Data.quotientBlocks (2 * i + 0) = (Data.quotientBlocks[i]!)[0]! :=
    bpt_eq (by norm_num)
  have e1 : bpt Data.quotientBlocks (2 * i + 1) = (Data.quotientBlocks[i]!)[1]! :=
    bpt_eq (by norm_num)
  have d0 : (2 * i + 0) / 2 = i := by omega
  have d1 : (2 * i + 1) / 2 = i := by omega
  have p0 := bpos_spec.2 (2 * i + 0) (by omega)
  have p1 := bpos_spec.2 (2 * i + 1) (by omega)
  rw [e0, d0] at p0
  rw [e1, d1] at p1
  have hd := all_range hpt (2 * i + 1) (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  have hd' := all_range hd.2 (2 * i + 0) (by omega)
  rw [e0, e1] at hd'
  have s2 := all_range h2 i hi
  simp only [beq_iff_eq] at s2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨⟨⟨⟨s2, bpt_lt hi (by norm_num)⟩, bpt_lt hi (by norm_num)⟩, by simpa using hd'⟩, p0⟩, p1⟩

end CertificateChecks.KernelSpor.ON3

end
