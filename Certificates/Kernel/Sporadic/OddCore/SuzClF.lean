module

public import Certificates.Kernel.Sporadic.OddCore.SuzClD
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EG
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckClosure
public import CFSG.Certificates.Kernel.B0SuzK.Glue
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzClF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native
open CFSG.Sporadic.SuzRecog.SuzL34Cert
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11
local notation "LT" => SuzClL
local notation "MT" => SuzClM

@[expose] noncomputable def bpK (G : Nat → Nat) (i : Nat) : Nat :=
  (List.range 4).foldl (fun R k => if i.testBit k then pc R (G k) else R) Id

@[expose] noncomputable def ppK (X : Nat) : Bool :=
  CFSG.KC.Enum.permOK 1782 11 (mask 11) (1782 * 11) X (pinvS 1782 11 (mask 11) X)

@[expose] noncomputable def tabsK (T : Nat → Nat) (ds : List (List Nat × Nat)) : Bool :=
  allN 4 (fun k => Nat.beq (T (2 ^ k)) (decK (ds.getD k ([], 0)))) &&
    allN 16 (fun i => Nat.beq (T i) (bpK (fun k => T (2 ^ k)) i) && ppK (T i) &&
      Nat.beq (pc (T i) (T i)) Id) &&
    allN 16 (fun i => allN 16 fun j => Nat.beq (T (Nat.xor i j)) (pc (T i) (T j))) &&
    allN 16 (fun i => allN i fun j => !Nat.beq (T i) (T j))

theorem kL : tabsK LT l1Decs = true := by quickRfl

theorem kM : tabsK MT m21Decs = true := by quickRfl

theorem kHdK : penumHdK Id SuzClK.cnt 4 SuzClK.T SuzClK.PL = true := by quickRfl

theorem kSlK : penumSlK 1782 11 (mask 11) (1782 * 11) false SuzClK.G SuzClK.GI 2 SuzClK.cnt
    SuzClK.T SuzClK.PL SuzClK.POS SuzClK.SRT SuzClK.SRI 0 4 = true := by quickRfl

theorem kBindK : allN 2 (fun j => Nat.beq (SuzClK.G j) (decK (l1CompDecs.getD j ([], 0))) &&
    cn (SuzClK.G j) && ppK (SuzClK.G j)) = true := by quickRfl

theorem kCntK : SuzClK.cnt ≤ 4 := by decide

theorem andT {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem and2' {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem decs_get {l : List (List Nat × Nat)} {k : Nat} (hk : k < l.length) :
    (decs l)[k]! = decTab (l.getD k ([], 0)) := by
  unfold decs
  rw [getElem!_pos _ k (by simpa using hk), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ hk]

theorem decs_size (l : List (List Nat × Nat)) : (decs l).size = l.length := by
  simp [decs]

theorem pBit {B : Array Tab} (hs : B.size = 4) {G : Nat → Nat} (hg : ∀ k < 4, P B[k]! (G k))
    (i : Nat) : P (bitProd B i) (bpK G i) := by
  have key : ∀ l : List Nat, (∀ k ∈ l, k < 4) → ∀ r R, P r R →
      P (l.foldl (fun r k => if i.testBit k then comp 1782 r B[k]! else r) r)
        (l.foldl (fun R k => if i.testBit k then pc R (G k) else R) R) := by
    intro l
    induction l with
    | nil => exact fun _ _ _ h => h
    | cons a l ih =>
      intro hl r R h
      rw [List.foldl_cons, List.foldl_cons]
      refine ih (fun k hk => hl k (List.mem_cons_of_mem _ hk)) _ _ ?_
      by_cases hb : i.testBit a = true
      · simp only [hb, ↓reduceIte]
        exact pc' h (hg a (hl a List.mem_cons_self))
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact h
  unfold bitProd bpK
  rw [hs]
  exact key (List.range 4) (fun k hk => List.mem_range.1 hk) _ _ pId'

structure TabsFacts (T : Nat → Nat) (ds : List (List Nat × Nat)) : Prop where
  p : ∀ i < 16, P (bitProd (decs ds) i) (T i)
  gen : ∀ k < 4, P (decs ds)[k]! (T (2 ^ k))
  pp : ∀ i < 16, PP 1782 11 (T i)
  sq : ∀ i < 16, Nat.beq (pc (T i) (T i)) Id = true
  mul : ∀ i < 16, ∀ j < 16, Nat.beq (T (Nat.xor i j)) (pc (T i) (T j)) = true
  dist : ∀ i < 16, ∀ j < i, T i ≠ T j

theorem tabsFacts {T : Nat → Nat} {ds : List (List Nat × Nat)} (hl : ds.length = 4)
    (hd : ∀ k < 4, (∀ c ∈ (ds.getD k ([], 0)).1, c < 10) ∧ (ds.getD k ([], 0)).2 < 128)
    (h : tabsK T ds = true) : TabsFacts T ds := by
  unfold tabsK at h
  obtain ⟨h, h4⟩ := and2' h
  obtain ⟨h, h3⟩ := and2' h
  obtain ⟨h1, h2⟩ := and2' h
  have gen : ∀ k < 4, P (decs ds)[k]! (T (2 ^ k)) := fun k hk => by
    rw [decs_get (by omega)]
    exact p_eq (pDec (hd k hk).1 (hd k hk).2) (allN_spec h1 k hk)
  have hi := fun i (hi : i < 16) => and2' (and2' (allN_spec h2 i hi)).1
  have p : ∀ i < 16, P (bitProd (decs ds) i) (T i) := fun i hi' =>
    p_eq (pBit (by rw [decs_size, hl]) gen i) (hi i hi').1
  refine ⟨p, gen, fun i hi' => PP_of_permOK CFSG.KC.B0SuzK.szOK_1782 (hi i hi').2,
    fun i hi' => (and2' (allN_spec h2 i hi')).2,
    fun i hi' j hj => allN_spec (allN_spec h3 i hi') j hj, fun i hi' j hj e => ?_⟩
  have := allN_spec (allN_spec h4 i hi') j hj
  rw [e, Nat.beq_refl] at this
  exact absurd this (by decide)

theorem closure_true {T : Nat → Nat} {ds : List (List Nat × Nat)} (H : TabsFacts T ds)
    {A : Array Tab} (hA : A = Array.ofFn (n := 16) fun i => bitProd (decs ds) i.val) :
    (allBelow 4 (fun k => A[2 ^ k]! == (decs ds)[k]!) &&
      allBelow A.size (fun k => CFSG.Sporadic.SuzOddCore.permOK 1782 A[k]!) &&
      anyBelow A.size (fun k => A[k]! == idTab 1782) &&
      (allBelow A.size fun i =>
        allBelow A.size fun j =>
          anyBelow A.size fun k => A[k]! == comp 1782 A[i]! A[j]!) &&
      (allBelow A.size fun i =>
        anyBelow A.size fun k => comp 1782 A[i]! A[k]! == idTab 1782) &&
      decide A.toList.Nodup &&
      allBelow A.size (fun k => found (indexOf A) A A[k]!)) = true := by
  have hs : A.size = 16 := by rw [hA, Array.size_ofFn]
  have hg : ∀ i < 16, P A[i]! (T i) := fun i hi => by
    rw [hA, ofFn_get (fun i => bitProd (decs ds) i) hi]
    exact H.p i hi
  have h0 : Nat.beq (T 0) Id = true := by
    have := H.mul 1 (by omega) 1 (by omega)
    rw [show Nat.xor 1 1 = 0 from rfl, Nat.eq_of_beq_eq_true (H.sq 1 (by omega))] at this
    exact this
  have anyB : ∀ {f : Nat → Bool} (k : Nat), k < 16 → f k = true → anyBelow 16 f = true :=
    fun {f} k hk h => by
      unfold anyBelow
      rw [List.any_eq_true]
      exact ⟨k, List.mem_range.2 (by omega), h⟩
  rw [hs]
  refine andT (andT (andT (andT (andT (andT ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · refine allBelow_of fun k hk => ?_
    rw [beqP (hg (2 ^ k) (by interval_cases k <;> decide)) (H.gen k hk)]
    exact Nat.beq_refl _
  · refine allBelow_of fun k hk => ?_
    rw [(hg k hk).1]
    exact CFSG.KC.B0SuzK.permOK_unpack (H.pp k hk)
  · refine anyB 0 (by omega) ?_
    rw [beqP (hg 0 (by omega)) pId']
    exact h0
  · refine allBelow_of fun i hi => allBelow_of fun j hj => ?_
    have hx : Nat.xor i j < 16 := Nat.xor_lt_two_pow (n := 4) hi hj
    refine anyB (Nat.xor i j) hx ?_
    rw [beqP (hg _ hx) (pc' (hg i hi) (hg j hj))]
    exact H.mul i hi j hj
  · refine allBelow_of fun i hi => anyB i hi ?_
    rw [beqP (pc' (hg i hi) (hg i hi)) pId']
    exact H.sq i hi
  · refine decide_eq_true ?_
    rw [hA, Array.toList_ofFn, List.nodup_ofFn]
    intro a b e
    simp only at e
    have eb := beqP (H.p a a.isLt) (H.p b b.isLt)
    rw [e, beq_self_eq_true] at eb
    have e' : T a = T b := Nat.eq_of_beq_eq_true eb.symm
    rcases Nat.lt_trichotomy a.val b.val with h | h | h
    · exact absurd e'.symm (H.dist b b.isLt a h)
    · exact Fin.ext h
    · exact absurd e' (H.dist a a.isLt b h)
  · refine allBelow_of fun k hk => ?_
    rw [found_indexOf_iff]
    exact ⟨k, by omega, rfl⟩

theorem l1Decs_ok : ∀ k < 4, (∀ c ∈ (l1Decs.getD k ([], 0)).1, c < 10) ∧
    (l1Decs.getD k ([], 0)).2 < 128 := by
  intro k hk
  interval_cases k <;> decide

theorem m21Decs_ok : ∀ k < 4, (∀ c ∈ (m21Decs.getD k ([], 0)).1, c < 10) ∧
    (m21Decs.getD k ([], 0)).2 < 128 := by
  intro k hk
  interval_cases k <;> decide

theorem l1CompDecs_ok : ∀ k < 2, (∀ c ∈ (l1CompDecs.getD k ([], 0)).1, c < 10) ∧
    (l1CompDecs.getD k ([], 0)).2 < 128 := by
  intro k hk
  interval_cases k <;> decide

theorem hL : TabsFacts LT l1Decs := tabsFacts rfl l1Decs_ok kL

theorem hM : TabsFacts MT m21Decs := tabsFacts rfl m21Decs_ok kM

theorem l1Tabs_eq : l1Tabs () = Array.ofFn (n := 16) fun i => bitProd (decs l1Decs) i.val := rfl

theorem m21Tabs_eq : m21Tabs () = Array.ofFn (n := 16) fun i => bitProd (decs m21Decs) i.val :=
  rfl

theorem l1TabsClosureCheck_true : l1TabsClosureCheck () = true := by
  unfold l1TabsClosureCheck
  exact closure_true hL l1Tabs_eq

theorem all_permOK {ds : List (List Nat × Nat)} {G : Nat → Nat}
    (h : ∀ k < ds.length, P (decs ds)[k]! (G k) ∧ PP 1782 11 (G k)) :
    ds.all (fun d => CFSG.Sporadic.SuzOddCore.permOK 1782 (decTab d)) = true := by
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  have e := decs_get hk
  rw [List.getD_eq_getElem _ _ hk] at e
  rw [← e, (h k hk).1.1]
  exact CFSG.KC.B0SuzK.permOK_unpack (h k hk).2

theorem bindK {j : Nat} (hj : j < 2) : P (decs l1CompDecs)[j]! (SuzClK.G j) ∧
    PP 1782 11 (SuzClK.G j) := by
  have h := allN_spec kBindK j hj
  obtain ⟨h, hp⟩ := and2' h
  obtain ⟨hb, -⟩ := and2' h
  rw [decs_get (by simpa [l1CompDecs] using hj)]
  exact ⟨p_eq (pDec (l1CompDecs_ok j hj).1 (l1CompDecs_ok j hj).2) hb,
    PP_of_permOK CFSG.KC.B0SuzK.szOK_1782 hp⟩

theorem gK : GensOK 1782 11 2 SuzClK.G (decs l1CompDecs) :=
  ⟨by rw [decs_size]; rfl, fun j hj => ⟨(bindK hj).1.1, (bindK hj).1.2⟩⟩

theorem ptK : ∀ i < SuzClK.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false SuzClK.G SuzClK.GI
    2 SuzClK.cnt SuzClK.T SuzClK.PL SuzClK.POS SuzClK.SRT SuzClK.SRI i = true :=
  fun i hi => penumSl_spec kSlK i (Nat.zero_le _) (by have := kCntK; omega) hi

theorem enumK : enumOK 1782 (decs l1CompDecs) (enumBFS 1782 (decs l1CompDecs) 4) = true := by
  obtain ⟨e, h⟩ := penumK_left_sound kSz gK kHdK ptK
  rw [e]
  exact h

theorem m21KClosureCheck_true : m21KClosureCheck () = true := by
  unfold m21KClosureCheck
  have hc := closure_true hM m21Tabs_eq
  simp only [Bool.and_eq_true] at hc ⊢
  obtain ⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩ := hc
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, ?_⟩, enumK⟩
  · exact all_permOK fun k hk => ⟨hM.gen k (by simpa [m21Decs] using hk),
      hM.pp _ (by have : k < 4 := by simpa [m21Decs] using hk
                  interval_cases k <;> decide)⟩
  · exact all_permOK fun k hk => bindK (by simpa [l1CompDecs] using hk)

end CertificateChecks.KernelSpor.SuzClF

end
