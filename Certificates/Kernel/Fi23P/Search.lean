module

public import Certificates.Kernel.Fi23P.Tables
public import Certificates.Kernel.Fi23P.Facts
public import Certificates.Kernel.Fi23P.Cnt
public import CFSG.Certificates.Kernel.Fi23P.BfsSound
import Certificates.Kernel.Fi23R.Sound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib
public import CFSG.Sporadic.Fi23.Class
public import CFSG.Sporadic.Fi23.Simple

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23P CFSG.KD.Fi23K CFSG.KD.Fi23P CFSG.KS.TW
  CFSG.Sporadic.Th.Native CFSG.Monster.Existence.Fi23Sp8.Native CFSG.KS.Raw.Orb
  CFSG.Sporadic.Bridge.Fi23GPL.Native

@[expose, irreducible] noncomputable def labA : Array Nat :=
  Array.ofFn (n := 31671) fun i => labP i.val
@[expose, irreducible] noncomputable def parA : Array Nat :=
  Array.ofFn (n := 31671) fun i => parP i.val
@[expose, irreducible] noncomputable def genA : Array Nat :=
  Array.ofFn (n := 31671) fun i => genP i.val
@[expose, irreducible] noncomputable def vecA : Array Nat :=
  Array.ofFn (n := 31671) fun i => vecG i.val

theorem ofFn_get {f : Nat → Nat} (x : Nat) :
    (Array.ofFn (n := 31671) fun i => f i.val)[x]! = if x < 31671 then f x else 0 := by
  split_ifs with h
  · rw [getElem!_pos _ x (by simpa using h), Array.getElem_ofFn]
  · rw [getElem!_neg _ x (by simpa using h)]
    rfl

theorem labA_get (x : Nat) : labA[x]! = labG x := by
  unfold labA
  exact ofFn_get x
theorem parA_get (x : Nat) : parA[x]! = parG x := by
  unfold parA
  exact ofFn_get x
theorem genA_get (x : Nat) : genA[x]! = genG x := by
  unfold genA
  exact ofFn_get x

theorem vecA_get (x : Nat) : vecA[x]! = vecG x := by
  unfold vecA
  rw [ofFn_get]
  split_ifs with h
  · rfl
  · unfold vecG
    rw [if_neg fun h' => h h'.1]

theorem mem_gIdx {k : Nat} : k ∈ gIdx () ↔ gOK k = true := by
  rw [gOK_iff]
  simp only [gIdx, List.mem_cons, List.not_mem_nil, or_false]
  omega

section


theorem IT_T : ∀ k ∈ gIdx (), ∀ x < 31671, ap IT[k]! x = TG k x := by
  intro k hk x hx
  rw [IT_ap, XK_eq ((gOK_iff k).1 (mem_gIdx.1 hk)).1 hx]
  rfl

theorem TG_inv : ∀ k ∈ gIdx (), ∀ x < 31671, TG k x < 31671 ∧ TG k (TG k x) = x := by
  intro k hk x hx
  have hk' := ((gOK_iff k).1 (mem_gIdx.1 hk)).1
  exact ⟨rng k (by omega) x hx, x_inv hk' hx⟩

theorem orb_eq : orbSearch IT [4777, 16688, 0] = (labA, parA, genA) := by
  unfold labA parA genA
  exact orbSearch_eq (rt := rtP) IT_T TG_inv bfs_ok

end

theorem pathWord_eq (r : Nat) : ∀ f p, pathWord parA genA r f p = pathF r f p
  | 0, _ => rfl
  | f + 1, p => by
    simp only [pathWord, pathF, parA_get, genA_get, pathWord_eq r f]

theorem imgLetter_ap (z : Int)
    (x : Nat) : ap (imgLetter IT IV z) x = XK (zIdx z) x := by
  unfold imgLetter zIdx
  split_ifs
  · exact IT_ap _ x
  · exact IV_ap _ x

theorem evalWord_eq :
    ∀ (w : List Int) (q : Nat), evalWord IT IV w q = wK w q
  | [], _ => rfl
  | z :: w, q => by
    change ap (imgLetter IT IV z) (evalWord IT IV w q) = XK (zIdx z) (wK w q)
    rw [imgLetter_ap, evalWord_eq w q]

@[expose] def SOK (S : Search) : Prop :=
  S.roots = rootsA ∧ S.lab = labA ∧ S.par = parA ∧ S.gen = genA

theorem pathW_eq {S : Search} (hS : SOK S) (p : Nat) : pathW S p = pathK p := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  unfold pathW pathK
  rw [h1, h2, h3, h4, labA_get, pathWord_eq]

theorem conjAct_eq (u : List Int)
    (q : Nat) : conjAct IT IV u q = conjK u q := by
  unfold conjAct conjK
  rw [evalWord_eq, evalWord_eq, IT_ap]

theorem commPt_eq {S : Search}
    (hS : SOK S) : commPt IT IV S = commK := by
  funext p q
  unfold commPt commK
  rw [pathW_eq hS, conjAct_eq]

theorem sig_facts : (∀ i < 255, tb L 7 i < 31671 ∧ labP (tb L 7 i) = 0) ∧
    ∀ i < 254, tb L 7 i < tb L 7 (i + 1) := by
  have h := allN_iff.1 sig_ok
  have hp : ∀ i < 255, tb L 7 i < 31671 ∧ labP (tb L 7 i) = 0 ∧
      (i < 254 → tb L 7 i < tb L 7 (i + 1)) := by
    intro i hi
    have hi' := h i hi
    rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true, bIf_eq] at hi'
    obtain ⟨h1, h2, h3⟩ := hi'
    refine ⟨by simpa [Nat.blt_eq] using h1, Nat.eq_of_beq_eq_true h2, fun hlt => ?_⟩
    rw [if_pos (by simpa [Nat.blt_eq] using hlt)] at h3
    simpa [Nat.blt_eq] using h3
  exact ⟨fun i hi => ⟨(hp i hi).1, (hp i hi).2.1⟩, fun i hi => (hp i (by omega)).2.2 hi⟩

theorem sigR_mono : ∀ j, j < 255 → ∀ i < j, tb L 7 i < tb L 7 j
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, hj, i, hi => by
    have h := sig_facts.2 j (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
    · exact lt_trans (sigR_mono j (by omega) i h') h
    · rw [h']
      exact h

theorem sigL_pairwise : sigL.Pairwise (· < ·) := by
  unfold sigL
  rw [List.pairwise_map]
  exact (List.pairwise_lt_range (n := 255)).imp_of_mem fun ha hb hab =>
    sigR_mono _ (List.mem_range.1 hb) _ hab

noncomputable abbrev FL : List Nat := (List.range 31671).filter fun p => labG p == 0

theorem FL_length : FL.length = 255 := by
  rw [← List.countP_eq_length_filter]
  have h := Nat.eq_of_beq_eq_true cnt_ok0
  rw [CertificateChecks.KernelFi23R.cntS_eq] at h
  simp only [Nat.zero_add, List.map_id'] at h
  rw [← h]
  apply List.countP_congr
  intro x hx
  have hx' := List.mem_range.1 hx
  simp [labG, hx']

theorem mem_FL {x : Nat} : x ∈ FL ↔ x < 31671 ∧ labP x = 0 := by
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    simpa [labG, h1] using h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simp [labG, h1, h2]⟩

theorem sigL_sub : sigL ⊆ FL := by
  intro x hx
  unfold sigL at hx
  rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact mem_FL.2 (sig_facts.1 i (List.mem_range.1 hi))

theorem FL_eq : FL = sigL := by
  have hs : List.Sublist sigL FL := List.sublist_of_subperm_of_pairwise
    (sigL_pairwise.nodup.subperm sigL_sub) (sigL_pairwise.imp le_of_lt)
    ((List.Pairwise.filter _ (List.pairwise_lt_range (n := 31671))).imp le_of_lt)
  refine (hs.eq_of_length ?_).symm
  rw [FL_length]
  simp [sigL]

theorem mem_sigL {x : Nat} : x ∈ sigL ↔ x < 31671 ∧ labP x = 0 := by
  rw [← FL_eq, mem_FL]

theorem sigList_eq {S : Search} (hS : SOK S) : sigList S = sigL := by
  unfold sigList
  rw [hS.2.1]
  simp only [labA_get]
  exact FL_eq

@[expose] noncomputable def SK : Search := ⟨#[4777, 16688, 0], labA, parA, genA, vecA, ptA⟩

theorem SK_ok : SOK SK := by
  unfold SOK SK
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem vec_pt {p : Nat} (hp : p ∈ sigL) : vecOfPt commK bLit p = tb L 5 p := by
  unfold sigL at hp
  rw [List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact beq_iff_eq.1 (List.all_eq_true.1 vec_ok i hi)

theorem vecs_eq : (Array.ofFn (n := 31671) fun p =>
    if labA[p.val]! == 0 then vecOfPt commK bLit p.val else 0) = vecA := by
  unfold vecA
  refine congrArg (Array.ofFn (n := 31671)) (funext fun p => ?_)
  rw [labA_get]
  unfold labG vecG
  rw [if_pos p.isLt]
  by_cases h : labP p.val = 0
  · rw [if_pos (by simp [h]), if_pos ⟨p.isLt, h⟩, vec_pt (mem_sigL.2 ⟨p.isLt, h⟩)]
  · rw [if_neg (by simp [h]), if_neg fun h' => h h'.2]

noncomputable abbrev ptF : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate 256 0
  for p in sigL do
    r := r.set! (vecG p) p
  return r

theorem ptOf_beq : (ptF.toList == ptA.toList) = true := by quickRfl

theorem ptOf_eq : ptF = ptA := Array.toList_inj.1 (beq_iff_eq.1 ptOf_beq)

end CertificateChecks.KernelFi23P

end
