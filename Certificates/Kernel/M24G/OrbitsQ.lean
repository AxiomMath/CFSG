module

public import Certificates.Kernel.M24G.LookPack
public import Certificates.Kernel.M24G.ReplayChunk
public import Certificates.Kernel.M24G.StepTabData

public section

namespace CFSG.KC.M24G.OrbQ

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G ReplayQ

@[expose] def decEqNQ : DecidableEq Nat := fun a b =>
  decidable_of_iff (Nat.beq a b = true) ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

@[expose] def reachKB (n : Nat) (steps : List (Nat → Nat)) (p : Nat) (c : List Nat)
    (r : List Nat × List Nat × List Nat) : Bool :=
  @replayOKB Nat decEqNQ id steps p 5000 r.1 r.2.1 r.2.2 (posTreeB id r.1) &&
    r.1.all (fun x => Nat.blt x n) && c.all fun q => (maskL r.1).testBit q

@[expose] def classOrbitKB (n : Nat) (cls : List (List Nat)) (sizes : List Nat)
    (steps : List (Nat → Nat)) (runs : List (List Nat × List Nat × List Nat)) : Bool :=
  let ms := cls.map maskL
  cls.length == sizes.length && runs.length == sizes.length &&
    (List.range n).all (fun p => (ms.filter fun m => m.testBit p).length == 1) &&
    ((cls.zip sizes).zip runs).all fun x => x.1.1.length == x.1.2 &&
      match x.1.1 with
      | [] => false
      | p :: _ => reachKB n steps p x.1.1 x.2

theorem reachK_eq_B : @reachK = @reachKB := by
  funext n steps p c r
  unfold reachK reachKB
  have hb : (fun x => decide (x < n)) = fun x => Nat.blt x n := by
    funext x
    cases h : Nat.blt x n
    · exact decide_eq_false fun hl => by rw [Nat.blt_eq.mpr hl] at h; cases h
    · exact decide_eq_true (Nat.blt_eq.mp h)
  rw [replayOK_eq_B, posTree_eq_B, replayOKB_inst _ decEqNQ, hb]

theorem classOrbitK_eq_B : @classOrbitK = @classOrbitKB := by
  funext n cls sizes steps runs
  unfold classOrbitK classOrbitKB
  rw [reachK_eq_B]
  rfl

@[expose] def clsOneB (n : Nat) (steps : List (Nat → Nat)) (c : List Nat) (k : Nat)
    (r : List Nat × List Nat × List Nat) : Bool :=
  c.length == k && match c with
    | [] => false
    | p :: _ => reachKB n steps p c r

@[expose] def clsPartB (n : Nat) (cls : List (List Nat)) (sizes : List Nat)
    (runs : List (List Nat × List Nat × List Nat)) : Bool :=
  cls.length == sizes.length && runs.length == sizes.length &&
    (List.range n).all (fun p => ((cls.map maskL).filter fun m => m.testBit p).length == 1)

theorem classOrbitKB_of {n : Nat} {cls : List (List Nat)} {sizes : List Nat}
    {steps : List (Nat → Nat)} {runs : List (List Nat × List Nat × List Nat)}
    (hp : clsPartB n cls sizes runs = true)
    (hk : ∀ k, k < sizes.length →
      clsOneB n steps (cls.getD k []) (sizes.getD k 0) (runs.getD k ([], [], [])) = true) :
    classOrbitKB n cls sizes steps runs = true := by
  unfold clsPartB at hp
  unfold classOrbitKB
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  simp only [h1, h2, beq_self_eq_true, h3, Bool.true_and, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_zip] at hi
  have hc := hk i (by omega)
  have e1 : i < cls.length := by omega
  have e2 : i < sizes.length := by omega
  have e3 : i < runs.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem e1, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem e2, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem e3, Option.getD_some] at hc
  simp only [List.getElem_zip]
  exact hc

theorem clsOneB_of {n : Nat} {steps : List (Nat → Nat)} {c : List Nat} {k : Nat}
    {r : List Nat × List Nat × List Nat} (hne : c.isEmpty = false) (hlen : (c.length == k) = true)
    (hrep : @replayOKB Nat decEqNQ id steps (c.headD 0) 5000 r.1 r.2.1 r.2.2 (posTreeB id r.1) = true)
    (hlt : r.1.all (fun x => Nat.blt x n) = true)
    (hm : c.all (fun q => (maskL r.1).testBit q) = true) : clsOneB n steps c k r = true := by
  cases c with
  | nil => cases hne
  | cons p cs =>
    unfold clsOneB reachKB
    simp only [List.headD] at hrep
    simp only [hlen, hrep, hlt, hm, Bool.and_self]

@[expose] def trioStepF (TL : List (Nat × Nat × Nat)) (tr : Nat → Nat × Nat × Nat) (g : Array Nat)
    (i : Nat) : Nat :=
  match findKB (Native.key3 (imgTrioF g.toList (tr i))) (posTreeB Native.key3 TL) with
  | some q => q
  | none => Native.nTrio

theorem trioStepsK_eq_B (TL : List (Nat × Nat × Nat)) (tr : Nat → Nat × Nat × Nat)
    (gs : List (Array Nat)) : trioStepsK TL tr gs = gs.map (trioStepF TL tr) := by
  unfold trioStepsK trioStepF idxK
  simp only [findK_eq_B, posTree_eq_B]
  rfl

@[expose] def sextStepF (SL : List (List Nat)) (sl : Nat → List Nat) (g : Array Nat) (i : Nat) :
    Nat :=
  if i < Native.nSext then
    match findKB (Native.keyL (imgSextF g.toList (sl i))) (posTreeB Native.keyL SL) with
    | some q => q
    | none => Native.nSext
  else Native.sextIdx (Native.imgSext g (sl i))

theorem sextStepsK_eq_B (SL : List (List Nat)) (sl : Nat → List Nat) (gs : List (Array Nat)) :
    sextStepsK SL sl gs = gs.map (sextStepF SL sl) := by
  unfold sextStepsK sextStepF idxK
  simp only [findK_eq_B, posTree_eq_B]
  rfl

@[expose] def tabF (N W P : Nat) (s : Nat → Nat) (i : Nat) : Nat :=
  bif Nat.blt i N then fieldW W P i else s i

@[expose] def chkT (s : Nat → Nat) (W P a k : Nat) : Bool :=
  (List.range' a k).all fun i => Nat.beq (s i) (fieldW W P i)

theorem tabF_eq {s : Nat → Nat} {N W P : Nat} (h : chkT s W P 0 N = true) : tabF N W P s = s := by
  funext i
  unfold tabF
  cases hb : Nat.blt i N
  · rfl
  · unfold chkT at h
    rw [List.all_eq_true] at h
    have hi := h i (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using Nat.blt_eq.mp hb⟩)
    exact (Nat.eq_of_beq_eq_true hi).symm

theorem lTabs_map {β : Type} (f : Array Nat → β) : Native.lTabs.map f =
    [f (Native.lTabs.getD 0 #[]), f (Native.lTabs.getD 1 #[]), f (Native.lTabs.getD 2 #[]),
      f (Native.lTabs.getD 3 #[])] := rfl

theorem uTabs_map {β : Type} (f : Array Nat → β) : Native.uTabs.map f =
    [f (Native.uTabs.getD 0 #[]), f (Native.uTabs.getD 1 #[]), f (Native.uTabs.getD 2 #[]),
      f (Native.uTabs.getD 3 #[])] := rfl

@[expose] def deltaBFQ (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat) (p₀ p : Nat) :
    List Bool :=
  let l := tr p₀
  let k := tr p
  [p == p₀, p != p₀ && Native.meets l k,
    !(Native.meets l k) && (ts p₀).any (fun q => (maskL (ts p)).testBit q),
    Native.zc l k == 1, Native.zc l k == 0]

theorem deltaBF_eq_Q : @deltaBF = @deltaBFQ := by
  funext tr ts p₀ p
  unfold deltaBF deltaBFQ
  simp only [LookQ.contains_eq_maskL]

@[expose] def deltaCls (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat) : List (List Nat) :=
  (List.range 5).map fun i =>
    (((List.range Native.nTrio).map fun p => (p, deltaBF tr ts 0 p)).filter
      fun e => e.2.getD i false).map (·.1)

theorem deltaCkF_split (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat)
    (orb : List (List Nat) → Bool) :
    deltaCkF tr ts orb = (deltaCkF tr ts (fun _ => true) && orb (deltaCls tr ts)) := by
  unfold deltaCkF deltaCls
  dsimp only
  generalize orb _ = b
  cases b <;> simp only [Bool.and_true, Bool.and_false, Bool.false_and]

@[expose] def kappaCls (sl : Nat → List Nat) (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat)
    (xi1 : Nat → Bool) : List (List Nat) :=
  (List.range 4).map fun i =>
    (((List.range Native.nTrio).map fun p => (p, kappaBF sl tr ts xi1 0 p)).filter
      fun e => e.2.getD i false).map (·.1)

theorem sextFactsF_eq (sl : Nat → List Nat) (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat)
    (xi1 : Nat → Bool) (u0 : Bool) (orbS orbT : List (List Nat) → Bool) :
    sextFactsF sl tr ts xi1 u0 orbS orbT = (u0 && orbS (xiCls sl) && orbT (kappaCls sl tr ts xi1)) :=
  rfl

@[expose] def commonOctsQ (s s' : List Nat) : Nat :=
  ((Native.octsS s).filter fun o => (Native.octsS s').any (Nat.beq o)).length

theorem contains_eq_any_beq (L : List Nat) (o : Nat) : L.contains o = L.any (Nat.beq o) := by
  rw [List.contains_eq_any_beq]
  congr 1

theorem commonOcts_eq_Q : @Native.commonOcts = @commonOctsQ := by
  funext s s'
  unfold Native.commonOcts commonOctsQ
  simp only [contains_eq_any_beq]

theorem any_beq_mod (L : List Nat) (o p : Nat) :
    L.any (Nat.beq o) = ((maskL (L.map (· % p))).testBit (o % p) && L.any (Nat.beq o)) := by
  cases h : L.any (Nat.beq o)
  · rw [Bool.and_false]
  · rw [Bool.and_true, ← LookQ.contains_eq_maskL]
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp h
    rw [Nat.eq_of_beq_eq_true he]
    exact (List.contains_iff_mem.mpr (List.mem_map_of_mem (f := (· % p)) hx)).symm

@[expose] def commonOctsH (s s' : List Nat) : Nat :=
  ((Native.octsS s).filter fun o =>
    (maskL ((Native.octsS s').map (· % 1021))).testBit (o % 1021) &&
      (Native.octsS s').any (Nat.beq o)).length

theorem commonOctsQ_eq_H : @commonOctsQ = @commonOctsH := by
  funext s s'
  unfold commonOctsQ commonOctsH
  simp only [← any_beq_mod]

@[expose] def xiBFQ (sl : Nat → List Nat) (q₀ q : Nat) : List Bool :=
  let c := commonOctsH (sl q₀) (sl q)
  [q == q₀, c == 3, c == 1, c == 0]

@[expose] def xiClsQ (sl : Nat → List Nat) : List (List Nat) :=
  (List.range 4).map fun i =>
    (((List.range Native.nSext).map fun q => (q, xiBFQ sl 0 q)).filter fun e => e.2.getD i false).map
      (·.1)

theorem xiCls_eq_Q : @xiCls = @xiClsQ := by
  funext sl
  unfold xiCls xiClsQ xiBF xiBFQ
  rw [commonOcts_eq_Q, commonOctsQ_eq_H]

@[expose] def kappaBFQ (sl : Nat → List Nat) (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat)
    (xi1 : Nat → Bool) (q₀ p : Nat) : List Bool :=
  let u := Native.octsS (sl q₀)
  let c := ((Native.octsT (tr p)).filter fun o => u.any (Nat.beq o)).length
  let inXi1 := (ts p).any xi1
  [(Native.octsT (tr p)).all (fun o => (Native.octsS (sl q₀)).any (Nat.beq o)), c == 1,
    c == 0 && inXi1, c == 0 && !inXi1]

theorem kappaBF_eq_Q : @kappaBF = @kappaBFQ := by
  funext sl tr ts xi1 q₀ p
  unfold kappaBF kappaBFQ Native.trioIn
  simp only [contains_eq_any_beq]

@[expose] def kappaClsQ (sl : Nat → List Nat) (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat)
    (xi1 : Nat → Bool) : List (List Nat) :=
  (List.range 4).map fun i =>
    (((List.range Native.nTrio).map fun p => (p, kappaBFQ sl tr ts xi1 0 p)).filter
      fun e => e.2.getD i false).map (·.1)

theorem kappaCls_eq_Q : @kappaCls = @kappaClsQ := by
  funext sl tr ts xi1
  unfold kappaCls kappaClsQ
  rw [kappaBF_eq_Q]

@[expose] def deltaRow (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat) (p : Nat) : Bool :=
  ((ts 0).any (fun q => (ts p).contains q) ==
      ((deltaBF tr ts 0 p).getD 0 false || (deltaBF tr ts 0 p).getD 1 false ||
        (deltaBF tr ts 0 p).getD 2 false)) &&
    deltaBF tr ts p 0 == deltaBF tr ts 0 p

theorem deltaCkF_rest (tr : Nat → Nat × Nat × Nat) (ts : Nat → List Nat) :
    deltaCkF tr ts (fun _ => true) =
      (Native.lTabs.all (fun g => Native.imgTrio g Native.baseTrio == Native.baseTrio) &&
        (List.range Native.nTrio).all (deltaRow tr ts)) := by
  unfold deltaCkF deltaRow
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_map, Bool.and_true, Bool.and_eq_true, List.all_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun p hp => ⟨h2 p hp, h3 p hp⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun p hp => (h2 p hp).1⟩, fun p hp => (h2 p hp).2⟩

@[expose] def allR (f : Nat → Bool) (a k : Nat) : Bool := (List.range' a k).all f

theorem all_range_eq (f : Nat → Bool) (n : Nat) : (List.range n).all f = allR f 0 n := by
  rw [allR, List.range_eq_range']

theorem allR_add (f : Nat → Bool) (a k₁ k₂ : Nat) :
    allR f a (k₁ + k₂) = (allR f a k₁ && allR f (a + k₁) k₂) := by
  unfold allR
  rw [← List.range'_append_1, List.all_append]

theorem allR_split (f : Nat → Bool) {a k : Nat} (k₁ k₂ b : Nat) (h₁ : k = k₁ + k₂)
    (h₂ : b = a + k₁) : allR f a k = (allR f a k₁ && allR f b k₂) := by
  rw [h₁, h₂, allR_add]

end CFSG.KC.M24G.OrbQ
