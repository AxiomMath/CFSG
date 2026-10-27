
module

public import Certificates.Kernel.Sporadic.OddCore.SuzWK
public import CFSG.Certificates.Kernel.Spor.FpBfsSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Kernel.Sporadic.L2.Vtx
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzWF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs CFSG.KC.B0SuzK
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.AS81.SuzB0
open CertificateChecks.KernelSpor CertificateChecks.KernelLC CertificateChecks.KernelSpor.SuzWK

theorem pg_lt {p i : Nat} (hp : canonK 1782 11 (mask 11) (1782 * 11) p = true) (hi : i < 1782) :
    pg 11 (mask 11) p i < 1782 := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  simpa [Nat.blt_eq] using allN_spec hp.2.2 i hi

theorem unpack_get {p i : Nat} (hi : i < 1782) : (unpack 1782 11 p)[i]! = pg 11 (mask 11) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem compA_get {t u : Array Nat} {x : Nat} (hx : x < 1782) :
    (compA 1782 t u)[x]! = t[u[x]!]! := by
  rw [compA, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem fp_of_get {a : Array Nat} {f : Nat → Nat} (h : ∀ x < 1782, a[x]! = f x) :
    fp a = fpOf f := by
  unfold fp
  rw [h 17 (by norm_num), h 333 (by norm_num), h 901 (by norm_num), h 1500 (by norm_num),
    h 1234 (by norm_num), h 77 (by norm_num)]
  rfl

theorem map_get {a : Array (Array Nat)} {f : Array Nat → Array Nat} {i : Nat} (hi : i < a.size) :
    (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem t1_eq : t1Arr = unpack 1782 11 (SuzInvT1.F 0) := SuzInv.run_eq1 (k := 0) (by norm_num)

theorem c_eq {k : Nat} (hk : k < 10) :
    (invInnerGenArrs 1)[k]! = unpack 1782 11 (SuzInvT1.F (18 + k)) := by
  have hic : invInnerGenCounts.getD 1 0 = 10 := rfl
  have his : invInnerStart 1 = 18 := rfl
  rw [getElem!_pos (invInnerGenArrs 1) k (by rw [invInnerGenArrs, Array.size_ofFn, hic]; exact hk)]
  simp only [invInnerGenArrs, Array.getElem_ofFn, his]
  exact SuzInv.run_eq1 (by omega)

theorem gens_eq {s : Nat} (hs : s < 2) : gens[s]! = unpack 1782 11 (SuzXS.F s) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzXS.all s hs
  rw [← SuzXS.eq] at h
  interval_cases s
  · simp only [gens, List.getElem!_toArray, List.getElem!_cons_zero]
    unfold CFSG.Sporadic.SuzRecog.LevelTwoData.xStrong
    exact h
  · simp only [gens, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    unfold CFSG.Sporadic.SuzRecog.LevelTwoData.xStrong
    exact h

theorem gi_eq {s : Nat} (hs : s < 2) : gensInv[s]! = unpack 1782 11 (SuzWGI s) := by
  have hg : gensInv[s]! = invCand 1782 gens[s]! := map_get (by simp [gens]; omega)
  rw [hg, gens_eq hs]
  interval_cases s
  · exact (invEqK_sound gi0).1
  · exact (invEqK_sound gi1).1

theorem pt_of {lo len i : Nat}
    (h : fpBfsPtSlK 1782 11 (mask 11) (1782 * 11) 2 343 SuzXS.F SuzWGI SuzWT SuzWV SuzWPL SuzWFP
      lo len = true) (h1 : lo ≤ i) (h2 : i < lo + len) (h3 : i < 343) (h4 : 0 < i) :
    fpBfsPtK 1782 11 (mask 11) (1782 * 11) 2 343 SuzXS.F SuzWGI SuzWT SuzWV SuzWPL SuzWFP i =
      true := by
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i 343 = true := Eq.mpr Nat.blt_eq h3
  have hz : Nat.beq i 0 = false := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rfl
  rw [hb, hz] at h'
  exact h'

theorem pts : ∀ i < 343, 0 < i →
    fpBfsPtK 1782 11 (mask 11) (1782 * 11) 2 343 SuzXS.F SuzWGI SuzWT SuzWV SuzWPL SuzWFP i =
      true := by
  intro i hi h0
  have hs : ∀ s < 11, ptK s = true := by
    intro s hs
    interval_cases s
    exacts [pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8, pt9, pt10]
  have h := hs (i / 32) (by omega)
  unfold ptK at h
  exact pt_of h (by change 32 * (i / 32) ≤ i; omega) (by change i < 32 * (i / 32) + 32; omega) hi h0

theorem steps : ∀ e < 353, fpBfsStK 11 (mask 11) 2 343 SuzXS.F SuzWGI SuzWT SuzWPL SuzWPOS SuzWFP e =
    true := by
  intro e he
  have h' := allN_spec st e he
  rw [strictB_eq] at h'
  have e' : Nat.add 0 e = e := Nat.zero_add e
  rw [e'] at h'
  have hb : Nat.blt e 353 = true := Eq.mpr Nat.blt_eq he
  rw [hb] at h'
  exact h'

theorem kWT : allN 343 (fun i => Nat.beq (L2A i) (SuzWT i)) = true := by quickRfl

theorem search : 343 ≤ aPts.size ∧ ∀ i < 343, aPts[i]! = unpack 1782 11 (SuzWT i) := by
  refine ⟨by rw [L2G.aPts_size]; norm_num, fun i hi => ?_⟩
  rw [(L2G.pA (L2G.hvA L2G.vtxOK) (by omega)).1, Nat.eq_of_beq_eq_true (allN_spec kWT i hi)]

theorem fp_aPts {i : Nat} (hi : i < 343) : fp aPts[i]! = SuzWFP i := by
  rw [search.2 i hi, fp_unpack]
  exact (Nat.eq_of_beq_eq_true (allN_spec fpT i hi)).symm

theorem bitB_eq (v i : Nat) : bitB v i = v.testBit i := by
  unfold bitB Nat.testBit
  change Nat.beq ((v >>> i) &&& 1) 1 = (1 &&& (v >>> i) != 0)
  rw [Nat.and_comm 1 (v >>> i), Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (v >>> i) with h | h <;> rw [h] <;> rfl

theorem fold_get (v : Nat) : ∀ k ≤ 6,
    ((List.range k).foldl (fun r i => if v.testBit i then compA 1782 r (qArr i) else r)
      (CFSG.PSL3Four.Native.idTab 1782)).size = 1782 ∧
    ∀ x < 1782, ((List.range k).foldl (fun r i => if v.testBit i then compA 1782 r (qArr i) else r)
      (CFSG.PSL3Four.Native.idTab 1782))[x]! = qPtK SuzB0Q.F v k x := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [CFSG.PSL3Four.Native.idTab], fun x hx => ?_⟩
    rw [List.range_zero, List.foldl_nil, CFSG.PSL3Four.Native.idTab,
      getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
    rfl
  | succ k ih =>
    intro hk
    obtain ⟨hs, hg⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hc := allN_spec canQ k (by omega)
    by_cases hb : v.testBit k = true
    · simp only [hb, ↓reduceIte]
      refine ⟨by simp [compA], fun x hx => ?_⟩
      rw [compA_get hx, B0Suz.q_eq (by omega), unpack_get hx, hg _ (pg_lt hc hx)]
      change _ = qPtK SuzB0Q.F v k (nIf(bitB v k, pg 11 (mask 11) (SuzB0Q.F k) x, x))
      rw [bitB_eq, hb]
    · rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hs, fun x hx => ?_⟩
      rw [hg x hx]
      change _ = qPtK SuzB0Q.F v k (nIf(bitB v k, pg 11 (mask 11) (SuzB0Q.F k) x, x))
      rw [bitB_eq, hb]

theorem qProd_get {v x : Nat} (hx : x < 1782) : (qProd v)[x]! = qPtK SuzB0Q.F v 6 x :=
  (fold_get v 6 le_rfl).2 x hx

theorem qf_get {v : Nat} (hv : v < 64) : SuzWQF (2 * v) = fp (qProd v) ∧
    SuzWQF (2 * v + 1) = fp (compA 1782 (qProd v) t1Arr) := by
  have h := allN_spec qf v hv
  rw [bAnd_iff] at h
  refine ⟨(Nat.eq_of_beq_eq_true h.1).trans (fp_of_get fun x hx => qProd_get hx).symm,
    (Nat.eq_of_beq_eq_true h.2).trans (fp_of_get fun x hx => ?_).symm⟩
  rw [compA_get hx, t1_eq, unpack_get hx, qProd_get (pg_lt canT hx)]

theorem foldl_contains (y : Nat) (a b : Nat → Nat) : ∀ (L : List Nat) (m : Std.HashSet Nat),
    (L.foldl (fun m v => (m.insert (a v)).insert (b v)) m).contains y =
      (m.contains y || L.any fun v => a v == y || b v == y)
  | [], m => by simp
  | v :: L, m => by
    rw [List.foldl_cons, foldl_contains y a b L, Std.HashSet.contains_insert,
      Std.HashSet.contains_insert, List.any_cons]
    cases a v == y <;> cases b v == y <;> cases m.contains y <;> simp

theorem q1Fp_eq : q1Fp = (List.range 64).foldl
    (fun m v => (m.insert (fp (qProd v))).insert (fp (compA 1782 (qProd v) t1Arr))) ∅ := by
  unfold q1Fp
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range_eq_range']

theorem contains_iff (y : Nat) : q1Fp.contains y = true ↔ ∃ j < 128, SuzWQF j = y := by
  rw [q1Fp_eq, foldl_contains]
  simp only [Std.HashSet.contains_empty, Bool.false_or, List.any_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨v, hv, h | h⟩
    · exact ⟨2 * v, by omega, (qf_get hv).1.trans h⟩
    · exact ⟨2 * v + 1, by omega, (qf_get hv).2.trans h⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j / 2, by omega, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · left
      rw [← (qf_get (v := j / 2) (by omega)).1]
      congr 1
      omega
    · right
      rw [← (qf_get (v := j / 2) (by omega)).2]
      congr 1
      omega

theorem p1_eq : p1 = 342 := by
  have hp := p1K
  rw [bAnd_iff, bAnd_iff] at hp
  obtain ⟨hA, hJ, hE⟩ := hp
  have hno : ∀ i, 0 < i → i < 342 → q1Fp.contains (fp aPts[i]!) = false := by
    intro i h0 hi
    rw [fp_aPts (by omega)]
    cases hc : q1Fp.contains (SuzWFP i)
    · rfl
    · exfalso
      obtain ⟨j, hj, he⟩ := (contains_iff _).1 hc
      have h' := allN_spec hA i hi
      have hz : Nat.beq i 0 = false := by
        obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
        rfl
      rw [hz] at h'
      have h'' := allN_spec h' j hj
      rw [he, Nat.beq_refl] at h''
      exact Bool.false_ne_true h''
  have hyes : q1Fp.contains (fp aPts[342]!) = true := by
    rw [fp_aPts (by norm_num)]
    exact (contains_iff _).2 ⟨SuzWJ 0, by simpa [Nat.blt_eq] using hJ,
      (Nat.eq_of_beq_eq_true hE).symm⟩
  have hf : (List.range 2835).filter (fun i => i != 0 && q1Fp.contains (fp aPts[i]!)) =
      342 :: ((List.range 2492).map (343 + ·)).filter
        (fun i => i != 0 && q1Fp.contains (fp aPts[i]!)) := by
    have hm : ((342 + ·) ∘ Nat.succ) = (343 + ·) := by
      funext i
      simp only [Function.comp, Nat.succ_eq_add_one]
      omega
    rw [(by norm_num : (2835 : Nat) = 342 + (2492 + 1)), List.range_add,
      List.range_succ_eq_map (n := 2492), List.map_cons, List.filter_append, List.filter_cons_of_pos (by simpa using hyes),
      List.filter_eq_nil_iff.2 (fun i hi => by
        have hi' := List.mem_range.1 hi
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · simp [h0]
        · simp [hno i h0 hi'])]
    rw [List.nil_append, List.map_map, hm, Nat.add_zero]
  unfold p1 o8Base
  rw [hf, List.getElem!_toArray, List.getElem!_cons_zero]

theorem qProd1_eq : qProd 1 = unpack 1782 11 (SuzB0Q.F 0) := by
  have h : qProd 1 = compA 1782 (CFSG.PSL3Four.Native.idTab 1782) (qArr 0) := by
    unfold qProd
    simp [List.range_succ, Nat.testBit]
  have hid : CFSG.PSL3Four.Native.idTab 1782 = unpack 1782 11 (pidn 1782 11) :=
    (idK_sound (by quickRfl)).symm
  rw [h, hid, B0Suz.q_eq (by norm_num), compEqK_sound wq]

theorem facts15116 : WCheck.wOK = true := by
  have h3 : (invInnerGenArrs 1)[3]! = unpack 1782 11 (SuzInvT1.F 21) := c_eq (by norm_num)
  have h6 : (invInnerGenArrs 1)[6]! = unpack 1782 11 (SuzInvT1.F 24) := c_eq (by norm_num)
  unfold WCheck.wOK WCheck.wConjArr WCheck.c3Arr WCheck.c6Arr
  rw [p1_eq, search.2 342 (by norm_num), t1_eq, compEqK_sound w0, h3, h6, (invEqK_sound ci0).1,
    (invEqK_sound ci1).1, compEqK_sound w1, qProd1_eq, compEqK_sound w2, compEqK_sound w3,
    compEqK_sound w4]
  exact eqK_sound wE

end CertificateChecks.KernelSpor.SuzWF

end
