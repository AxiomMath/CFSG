module

public import Certificates.Kernel.SchreierFam.C188002P
public import Certificates.Kernel.SchreierFam.C188002C
public import Certificates.Kernel.SchreierFam.C188002FG
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import Certificates.Data.HuppertU38.Model
public import CFSG.RankThree.PartOne.KS.PKit
public import Certificates.Certificate188002Base
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import Mathlib

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSchreierFam.U38

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Certificates.Kernel.U38 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native GF64

theorem fold_other (f : Nat → Nat) (p : Nat) :
    ∀ (L : List Nat) (t : Array Nat), (∀ j ∈ L, f j ≠ p) →
      (L.foldl (fun t i => t.set! (f i) i) t)[p]! = t[p]!
  | [], _, _ => rfl
  | x :: L, t, h => by
    rw [List.foldl_cons, fold_other f p L _ (fun j hj => h j (List.mem_cons_of_mem x hj))]
    have hx := h x List.mem_cons_self
    simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, hx]

theorem fold_size (f : Nat → Nat) :
    ∀ (L : List Nat) (t : Array Nat), (L.foldl (fun t i => t.set! (f i) i) t).size = t.size
  | [], _ => rfl
  | x :: L, t => by rw [List.foldl_cons, fold_size f L, Array.size_set!]

theorem foldl_set_get (f : Nat → Nat) :
    ∀ (L : List Nat) (t : Array Nat), (L.map f).Nodup → (∀ i ∈ L, f i < t.size) →
      ∀ i ∈ L, (L.foldl (fun t i => t.set! (f i) i) t)[f i]! = i
  | [], _, _, _, _, hi => absurd hi List.not_mem_nil
  | x :: L, t, hnd, hlt, i, hi => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hi
    · rw [fold_other f (f i) L _ (fun j hj e => hnd.1 (List.mem_map.2 ⟨j, hj, e⟩))]
      have hs := hlt i List.mem_cons_self
      simp [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds, hs]
    · exact foldl_set_get f L _ hnd.2
        (fun j hj => by rw [Array.size_set!]; exact hlt j (List.mem_cons_of_mem x hj)) i hi

theorem idx_get (i : Fin 513) : idxTable[vcode (ptsV i)]! = i.val := by
  have hnd : ((List.range 513).map fun i => vcode (ptsVn i)).Nodup := codesOK.1
  have hlt : ∀ i ∈ List.range 513, vcode (ptsVn i) < (Array.replicate 262144 0).size := by
    intro i hi
    have h := List.all_eq_true.1 codesOK.2 _ (List.mem_map.2 ⟨i, hi, rfl⟩)
    simpa using h
  exact foldl_set_get (fun i => vcode (ptsVn i)) _ _ hnd hlt i (List.mem_range.2 i.2)

theorem ofNat'_toNat (a : GF64) : ofNat' a.val.val = a :=
  eq_iff.2 (Nat.mod_eq_of_lt a.val.2)

theorem vcode_inj {v w : Fin 3 → GF64} (h : vcode v = vcode w) : v = w := by
  have h0 := (v 0).val.2
  have h1 := (v 1).val.2
  have h2 := (v 2).val.2
  have h3 := (w 0).val.2
  have h4 := (w 1).val.2
  have h5 := (w 2).val.2
  unfold vcode GF64.toNat at h
  funext j
  rw [eq_iff]
  unfold GF64.toNat
  fin_cases j <;> simp <;> omega

theorem ptsChk_at {x y z : Nat} (hx : x < 64) (hy : y < 64) (hz : z < 64) :
    ((ofNat' x == 0 && ofNat' y == 0 && ofNat' z == 0) ||
      !isoB (ofNat' x) (ofNat' y) (ofNat' z) ||
      codesL.contains (vcode (normV3 (ofNat' x) (ofNat' y) (ofNat' z)))) = true := by
  have hy' := List.mem_range.2 hy
  have hz' := List.mem_range.2 hz
  have slice : ∀ x0, ptsChk x0 16 = true → x0 ≤ x → x < x0 + 16 → _ := fun x0 h h1 h2 =>
    List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h x
      (List.mem_range'_1.2 ⟨h1, h2⟩)) y hy') z hz'
  rcases Nat.lt_or_ge x 16 with h | h
  · exact slice 0 chk0 (by omega) (by omega)
  rcases Nat.lt_or_ge x 32 with h' | h'
  · exact slice 16 chk1 h (by omega)
  rcases Nat.lt_or_ge x 48 with h'' | h''
  · exact slice 32 chk2 h' (by omega)
  · exact slice 48 chk3 h'' (by omega)

theorem iso_point (a b c : GF64) (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) (hi : Iso3 a b c) :
    ptsV (ptIdx idxTable[vcode (normV3 a b c)]!) = normV3 a b c := by
  have h := ptsChk_at a.val.2 b.val.2 c.val.2
  rw [ofNat'_toNat, ofNat'_toNat, ofNat'_toNat] at h
  have hz : (a == 0 && b == 0 && c == 0) = false := by
    rcases hn with h1 | h1 | h1 <;> simp [h1]
  have hiso : isoB a b c = true := by
    unfold Iso3 at hi
    rw [c8OK, c8OK, c8OK] at hi
    simp [isoB, hi]
  rw [hz, hiso, Bool.false_or, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
  obtain ⟨i, hi, e⟩ := List.mem_map.1 h
  have hv : ptsVn i = normV3 a b c := vcode_inj e
  have hi' := List.mem_range.1 hi
  rw [← hv]
  have := idx_get ⟨i, hi'⟩
  rw [ptsV] at this
  rw [this]
  simp [ptsV, ptIdx, Nat.mod_eq_of_lt hi']

theorem points : Certificates.Cert188002Points :=
  ⟨ptsOK, idx_get, iso_point⟩

theorem permArr_eq {k : Nat} (hk : k < 25) : permArr k = unpack 513 10 (PF k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound U38T.all k hk
  rw [← U38T.eq] at h
  exact h

theorem gensO_get {k : Nat} (hk : k < 9) : gensO[k]! = unpack 513 10 (PF k) := by
  rw [gensO, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  exact permArr_eq (by omega)

theorem unpack_get' {P i : Nat} (hi : i < 513) : (unpack 513 10 P)[i]! = pg 10 (mask 10) P i :=
  CFSG.KC.Misc.PairCount.unpack_get hi

theorem genAll {k : Nat} (hk : k < 7) : (List.range 513).all (actK k) = true := by
  match k, hk with
  | 0, _ => exact gen0
  | 1, _ => exact gen1
  | 2, _ => exact gen2
  | 3, _ => exact gen3
  | 4, _ => exact gen4
  | 5, _ => exact gen5
  | 6, _ => exact gen6

theorem gens : Certificates.Cert188002Gens := by
  refine ⟨rootsSU.2, fun k j => ?_⟩
  have hk := k.2
  have hj := j.2
  have h := List.all_eq_true.1 (genAll hk) j.val (List.mem_range.2 hj)
  have hg : genMatN k.val = genMat k := by rw [genMatN, dif_pos hk]
  rw [actK, hg] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hnz, hlt⟩, heq⟩ := h
  have heq' := vcode_inj (Nat.eq_of_beq_eq_true heq)
  refine ⟨?_, ⟨⟨pg 10 (mask 10) (PF k.val) j.val, Nat.le_of_ble_eq_true hlt⟩, ?_, heq'⟩⟩
  · by_contra hc
    simp only [not_or, not_not] at hc
    simp only [ptsV] at hc
    rw [hc.1, hc.2.1, hc.2.2] at hnz
    exact absurd hnz (by decide)
  · rw [gensO_get (by omega), unpack_get' hj]

theorem strong3_get {j : Nat} (hj : j < 11) : strong3[j]! = permArr (idx j) := by
  interval_cases j <;> rfl

theorem binds : Binds 513 10 U38C.S 11 4 U38C.BP strong3 base3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl, fun j hj => ?_, rfl, bget⟩
  have hidx : idx j < 25 := by unfold idx; split <;> omega
  rw [strong3_get hj, permArr_eq hidx, ← Nat.eq_of_beq_eq_true (allN_spec bS j hj)]

theorem words_eq : words3 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 7 11 d3 :=
  wordsArr_eq (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem allLt_iff' {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    simpa using h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i.1 i.2

theorem permF_at {k : Nat} (hk : k < 9) :
    permOK 513 10 (mask 10) (513 * 10) (PF k) (pinv (PF k)) = true ∧ cn (PF k) = true ∧
      cn (pinv (PF k)) = true := by
  have h := allN_spec permF k hk
  simpa only [bAnd_iff] using h

theorem siftC_at {a i : Nat} (ha : a < 2) (hi : i < 7) :
    sk (cjA (PF (7 + a)) (PF i)) = true ∧ sk (cjI (PF (7 + a)) (PF i)) = true ∧
      cn (cjA (PF (7 + a)) (PF i)) = true ∧ cn (cjI (PF (7 + a)) (PF i)) = true := by
  have h := allN_spec (allN_spec siftC a ha) i hi
  simpa only [bAnd_iff] using h

theorem ucomp {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    compA 513 (unpack 513 10 p) (unpack 513 10 q) = unpack 513 10 (pc p q) := by
  refine compEqK_sound ?_
  unfold compEqK
  rw [bAnd_iff, bAnd_iff]
  exact ⟨hp, hq, Nat.beq_refl _⟩

theorem ucn {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (pc p q) = true :=
  canonK_pcomp hp hq

theorem sift_of {g : Array Nat} {G : Nat} (hg : g = unpack 513 10 G) (hc : cn G = true)
    (h : sk G = true) : siftA 513 (rawLevels 513 strong3 base3) base3 0 g = true :=
  siftK_soundR binds perm U38C.hl hg (CFSG.KS.PF.canon_facts hc).2.2.1 (range_of_canonK hc) h

theorem chain : Certificates.Cert188002Chain := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [words_eq]
    exact rawChainK_sound binds U38C.head U38C.hl hNS U38C.hs
  · rw [rawOrbitSizesK_sound binds perm U38C.hl]
    exact orbs
  · refine allLt_iff'.2 fun k hk => ?_
    rw [gensO_get hk]
    obtain ⟨h1, -, -⟩ := permF_at hk
    obtain ⟨e1, i1⟩ := invEqK_sound h1
    unfold validA
    rw [e1]
    exact i1
  · refine allLt_iff'.2 fun a ha => allLt_iff'.2 fun i hi => ?_
    obtain ⟨s1, s2, c1, c2⟩ := siftC_at ha hi
    obtain ⟨g1, gc, gic⟩ := permF_at (k := 7 + a) (by omega)
    obtain ⟨-, yc, -⟩ := permF_at (k := i) (by omega)
    have hinv := (invEqK_sound g1).1
    rw [Bool.and_eq_true, gensO_get (by omega), gensO_get (by omega)]
    refine ⟨sift_of ?_ c1 s1, sift_of ?_ c2 s2⟩
    · rw [conjA, hinv, ucomp yc gic, ucomp gc (ucn yc gic)]
      rfl
    · rw [conjInvA, hinv, ucomp yc gc, ucomp gic (ucn yc gc)]
      rfl

end CertificateChecks.KernelSchreierFam.U38
