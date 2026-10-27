module

public import CFSG.Certificates.Kernel.U43Pk.CoverSound
public import CFSG.Certificates.Kernel.ArrBfsCert
public import Certificates.Kernel.U43Pk.CovPts
public import Certificates.Kernel.U43Pk.CovLists
import Certificates.Kernel.U43Pk.Facts
import CFSG.Certificates.Kernel.PackSetSound
import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelU43Pk

open CFSG.KD.U43Pk CFSG.KS.U43Pk CFSG.KS.ArrBfsSim CFSG.Monster.B.Fischer CFSG.KC.Enum
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check

theorem bfs_eq : bfs u43Data = cert 4 1024 (fun i => dec (T i)) E PA LA := by
  have hsz : u43Data.gens.size = 4 := rfl
  have hfuel : u43Data.fuel = 1100 := rfl
  obtain ⟨Tb, -, h0⟩ := tables_of (n := 4) (N := 1024) (by norm_num) gensEq gensV ptAll
  unfold bfs
  rw [hsz, hfuel, ← h0]
  exact arrBfs_eq Tb (by norm_num)

theorem blk_spec {f : ℕ → Bool} {w q : ℕ} (h : allBlk (Nat.mul w q) (fun i => strictB i f) w = true)
    {l : ℕ} (hl : l < w) : f (w * q + l) = true := by
  have e := CFSG.KC.Pack.allBlk_spec h l hl
  simp only [CFSG.KC.Pack.strictB_eq] at e
  exact e

theorem fmCongr {β : Type} {l : List ℕ} {f g : ℕ → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp), ih fun a ha => h a (by simp [ha])]

theorem clsAll : ∀ i < 1024, clsK (T i) = CL i := by
  have hb : ∀ q < 16, u43ClsBlk q = true := by
    intro q hq
    interval_cases q
    exacts [u43ClsBlk0, u43ClsBlk1, u43ClsBlk2, u43ClsBlk3, u43ClsBlk4, u43ClsBlk5, u43ClsBlk6,
      u43ClsBlk7, u43ClsBlk8, u43ClsBlk9, u43ClsBlk10, u43ClsBlk11, u43ClsBlk12, u43ClsBlk13,
      u43ClsBlk14, u43ClsBlk15]
  intro i hi
  have e := blk_spec (hb (i / 64) (by omega)) (Nat.mod_lt i (by norm_num : 64 > 0))
  rw [Nat.div_add_mod] at e
  exact Nat.eq_of_beq_eq_true e

theorem pairAll : ∀ a < 384, ∀ b < 191, pairK (WD a b) (T (OI a)) (T (II b)) = true := by
  have hb : ∀ q < 48, u43PairBlk q = true := by
    intro q hq
    interval_cases q
    exacts [u43PairBlk0, u43PairBlk1, u43PairBlk2, u43PairBlk3, u43PairBlk4, u43PairBlk5,
      u43PairBlk6, u43PairBlk7, u43PairBlk8, u43PairBlk9, u43PairBlk10, u43PairBlk11,
      u43PairBlk12, u43PairBlk13, u43PairBlk14, u43PairBlk15, u43PairBlk16, u43PairBlk17,
      u43PairBlk18, u43PairBlk19, u43PairBlk20, u43PairBlk21, u43PairBlk22, u43PairBlk23,
      u43PairBlk24, u43PairBlk25, u43PairBlk26, u43PairBlk27, u43PairBlk28, u43PairBlk29,
      u43PairBlk30, u43PairBlk31, u43PairBlk32, u43PairBlk33, u43PairBlk34, u43PairBlk35,
      u43PairBlk36, u43PairBlk37, u43PairBlk38, u43PairBlk39, u43PairBlk40, u43PairBlk41,
      u43PairBlk42, u43PairBlk43, u43PairBlk44, u43PairBlk45, u43PairBlk46, u43PairBlk47]
  intro a ha b hb'
  have e := blk_spec (hb (a / 8) (by omega)) (Nat.mod_lt a (by norm_num : 8 > 0))
  rw [Nat.div_add_mod, CFSG.KC.Pack.strictB_eq] at e
  have e2 := CFSG.KC.Pack.allBlk_spec e b hb'
  simp only [Nat.add_eq, Nat.zero_add, CFSG.KC.Pack.strictB_eq] at e2
  exact e2

theorem conjAll : ∀ k < 2304, conjC k = true := by
  have hb : ∀ q < 36, u43ConjBlk q = true := by
    intro q hq
    interval_cases q
    exacts [u43ConjBlk0, u43ConjBlk1, u43ConjBlk2, u43ConjBlk3, u43ConjBlk4, u43ConjBlk5,
      u43ConjBlk6, u43ConjBlk7, u43ConjBlk8, u43ConjBlk9, u43ConjBlk10, u43ConjBlk11,
      u43ConjBlk12, u43ConjBlk13, u43ConjBlk14, u43ConjBlk15, u43ConjBlk16, u43ConjBlk17,
      u43ConjBlk18, u43ConjBlk19, u43ConjBlk20, u43ConjBlk21, u43ConjBlk22, u43ConjBlk23,
      u43ConjBlk24, u43ConjBlk25, u43ConjBlk26, u43ConjBlk27, u43ConjBlk28, u43ConjBlk29,
      u43ConjBlk30, u43ConjBlk31, u43ConjBlk32, u43ConjBlk33, u43ConjBlk34, u43ConjBlk35]
  intro k hk
  have e := blk_spec (f := conjC) (hb (k / 64) (by omega)) (Nat.mod_lt k (by norm_num : 64 > 0))
  rwa [Nat.div_add_mod] at e

theorem rawT {i : ℕ} (hi : i < 1024) : rawValidK (T i) = true :=
  (validK_spec (ptK_spec (ptAll i hi)).1).1

theorem digT {i : ℕ} (hi : i < 1024) : Dig (T i) := (rawValidK_spec (rawT hi)).2.1

theorem ltT {i : ℕ} (hi : i < 1024) : T i < 16 ^ 17 := (rawValidK_spec (rawT hi)).1

theorem squares_get {A : Array (Array ℕ)} {i : ℕ} (hi : i < A.size) :
    (squares A)[i]! = mulRaw A[i]! A[i]! := by
  unfold squares
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos A i hi]

theorem squares_size (A : Array (Array ℕ)) : (squares A).size = A.size := by simp [squares]

theorem OI_lt {a : ℕ} (ha : a < 384) : OI a < 1024 := by
  have h : OI a ∈ (List.range 1024).filter o8D := by
    rw [o8L]
    exact List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem II_lt {b : ℕ} (hb : b < 191) : II b < 1024 := by
  have h : II b ∈ (List.range 1024).filter invD := by
    rw [invL]
    exact List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem eq_dec_of {x : Array ℕ} {P : ℕ} (h : x.size = 17 ∧ ∀ j < 17, x[j]! = dg P j) : x = dec P :=
  eq_dec h.1 h.2

theorem coverOK_true : coverOK u43Data = true := by
  set pts := (bfs u43Data).pts with hpd
  have hsz : pts.size = 1024 := by rw [hpd, bfs_eq, cert_pts_size]
  have hget : ∀ i < 1024, pts[i]! = dec (T i) := fun i hi => by rw [hpd, bfs_eq, cert_pts_get hi]
  have hsq : ∀ i < 1024, (squares pts)[i]! = dec (mulK (T i) (T i)) := fun i hi => by
    rw [squares_get (by omega), hget i hi, mulRaw_dec (digT hi) (digT hi)]
  have hsq2 : ∀ i < 1024, (squares (squares pts))[i]! =
      dec (mulK (mulK (T i) (T i)) (mulK (T i) (T i))) := fun i hi => by
    have d := mulK_dig (digT hi) (digT hi)
    rw [squares_get (by rw [squares_size]; omega), hsq i hi, mulRaw_dec d d]
  have hsq3 : ∀ i < 1024, (squares (squares (squares pts)))[i]! =
      dec (mulK (mulK (mulK (T i) (T i)) (mulK (T i) (T i)))
        (mulK (mulK (T i) (T i)) (mulK (T i) (T i)))) := fun i hi => by
    have d := mulK_dig (digT hi) (digT hi)
    have d2 := mulK_dig d d
    rw [squares_get (by rw [squares_size, squares_size]; omega), hsq2 i hi, mulRaw_dec d2 d2]
  have ho8 : orderEight (squares (squares pts)) (squares (squares (squares pts))) =
      (List.range 384).map OI := by
    rw [← o8L]
    unfold orderEight
    rw [squares_size, squares_size, hsz]
    apply List.filter_congr
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [hsq3 i hi', hsq2 i hi', isZ_dec (mulK_lt _ _), isZ_dec (mulK_lt _ _), ← clsK_o8]
    unfold o8D
    rw [clsAll i hi']
  have hinv : involutions pts (squares pts) = (List.range 191).map II := by
    rw [← invL]
    unfold involutions
    rw [hsz]
    apply List.filter_congr
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [hsq i hi', hget i hi', isZ_dec (mulK_lt _ _), isZ_dec (ltT hi'), ← clsK_inv]
    unfold invD
    rw [clsAll i hi']
  have hgood : goodPairs pts (squares pts) (squares (squares pts)) (squares (squares (squares pts))) =
      (List.range 2304).map fun k => (GI k, GJ k) := by
    rw [← gpL]
    unfold goodPairs
    rw [ho8, hinv, List.flatMap_map]
    apply fmCongr
    intro a ha
    have ha' := List.mem_range.1 ha
    beta_reduce
    rw [List.filter_map, List.map_map]
    have key : ∀ b ∈ List.range 191,
        ((fun j => eqZ (mulRaw pts[OI a]! pts[j]!) (mulRaw pts[j]! pts[OI a]!)) ∘ II) b =
          Nat.beq (WD a b) 65535 := by
      intro b hb
      have hb' := List.mem_range.1 hb
      simp only [Function.comp_apply]
      rw [hget _ (OI_lt ha'), hget _ (II_lt hb')]
      exact pairK_spec (digT (OI_lt ha')) (digT (II_lt hb')) (pairAll a ha' b hb')
    rw [List.filter_congr key]
    rfl
  have htab : u43Data.tab.toList = (List.range 2304).map fun k => (TR k, TS k) := by
    have h1 : u43Data.tab = tabOfString (String.ofList U43T.chars) := by rw [U43T.eq]
    rw [h1, tabOfString_ofList _ tabDigits]
    exact tabL
  have hts : u43Data.tab.size = 2304 := by rw [Array.size_eq_length_toList, htab]; simp
  have hreps := repsL
  unfold coverOK
  try simp only
  rw [← hpd, hgood, htab, List.zip_map', hts]
  simp only [List.length_map, List.length_range, beq_self_eq_true, Bool.true_and, List.all_eq_true,
    List.mem_map, List.mem_range, forall_exists_index, and_imp]
  rintro _ k hk rfl
  have hc := conjAll k hk
  unfold conjC at hc
  simp only [CFSG.KC.Pack.strictB_eq] at hc
  obtain ⟨h1, hc⟩ := bAnd_spec hc
  obtain ⟨h2, hc⟩ := bAnd_spec hc
  obtain ⟨h3, hc⟩ := bAnd_spec hc
  obtain ⟨h4, hc⟩ := bAnd_spec hc
  have hr : TR k < 48 := Eq.mp Nat.blt_eq h1
  have hs : TS k < 1024 := Eq.mp Nat.blt_eq h2
  have hi : GI k < 1024 := Eq.mp Nat.blt_eq h3
  have hj : GJ k < 1024 := Eq.mp Nat.blt_eq h4
  have hrd := CFSG.KC.Pack.allBlk_spec repDig (TR k) hr
  rw [Nat.add_eq, Nat.zero_add] at hrd
  obtain ⟨hdx, hdt⟩ := bAnd_spec hrd
  obtain ⟨e1, e2⟩ := conjK_spec (digT hs) (digT hi) (digT hj) (digK_spec hdx) (digK_spec hdt) hc
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by rw [hreps.1]; exact hr, by rw [hsz]; exact hs⟩, ?_⟩, ?_⟩
  · rw [hget _ hs, hget _ hi, eq_dec_of (hreps.2 _ hr).1]
    exact e1
  · rw [hget _ hs, hget _ hj, eq_dec_of (hreps.2 _ hr).2]
    exact e2

end CertificateChecks.KernelU43Pk

end
