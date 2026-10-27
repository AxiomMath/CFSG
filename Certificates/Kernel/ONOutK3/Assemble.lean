module

public import Certificates.Kernel.ONOutK3.Joins
public import Certificates.Kernel.ONOutK3.MatSound
public import Certificates.Kernel.Sporadic.ON3.Elements
public import CFSG.Certificates.Kernel.ONOutK3.WalkSound
public import CFSG.Certificates.Kernel.ONOutK3.TreeSound
public import CFSG.Certificates.Kernel.ONOutK3.FSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3 CFSG.KS.ONK3 CFSG.KS.Bfs3 CFSG.KS.BfsReplay
open CFSG.ComponentClassification.SolMax.ONOut
open CertificateChecks.KernelSpor.ON3 (mG m_get)

noncomputable abbrev G : Nat → Nat → Nat := CertificateChecks.KernelSpor.ON3.mG

theorem hN : ∀ s < 315, sliceOK G ONK3N UL UW FK TC s = true := fun s hs => nAll s hs

theorem hS : ∀ s < 64, sortSl ONK3N ONK3S s = true := fun s hs => sAll s hs

theorem hU : ∀ l < 3, Lets (UL l) (UW l) := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl <;> rfl

theorem vArrs_get : ∀ l < 3, ∀ x < 245520, (vArrs[l]!)[x]! = gword G (UL l) (UW l) x :=
  vArrs_of_mchk ONK3M fun c hc => mAll c hc

theorem hArrs_get {l : Nat} (hl : l < 3) {x : Nat} (hx : x < 245520) :
    (hArrs[l]!)[x]! = G l x ∧ G l x < 245520 := m_get hl x hx

noncomputable abbrev parN (k : Nat) : Nat := parF (nrec ONK3N k)
noncomputable abbrev labN (k : Nat) : Nat := labF (nrec ONK3N k)

theorem R3_congr {step step' : Nat → Pt3 → Pt3} {k : Nat} {root : Pt3} {cnt : Nat}
    {T : Nat → Pt3} {par lab : Nat → Nat} {pos : Nat → Nat → Nat}
    (R : R3 step k root cnt T par lab pos) (h : ∀ i < cnt, ∀ j < k, step' j (T i) = step j (T i)) :
    R3 step' k root cnt T par lab pos := by
  refine ⟨R.pos_cnt, R.root_eq, R.par_zero, R.lab_zero, R.inj, fun i h0 hi => ?_, R.order,
    fun i hi j hj => ?_⟩
  · obtain ⟨a, b, c⟩ := R.tree i h0 hi
    exact ⟨a, b, by rw [h _ (Nat.lt_trans a hi) _ b]; exact c⟩
  · obtain ⟨a, b, c⟩ := R.close i hi j hj
    exact ⟨a, by rw [h _ hi _ hj]; exact b, c⟩

theorem node_lt {k : Nat} (hk : k < 161280) :
    tA (nrec ONK3N k) < 245520 ∧ tB (nrec ONK3N k) < 245520 ∧ tC (nrec ONK3N k) < 245520 := by
  have := nodes_of hN (k := k) hk
  exact ⟨this.ltA, this.ltB, this.ltC⟩

theorem step_eq {l : Nat} (hl : l < 3) {k : Nat} (hk : k < 161280) :
    arrStep hArrs l (Tn ONK3N k) = stepG G l (Tn ONK3N k) := by
  obtain ⟨a, b, c⟩ := node_lt hk
  unfold arrStep stepG map3 Tn
  dsimp only
  rw [(hArrs_get hl a).1, (hArrs_get hl b).1, (hArrs_get hl c).1]

theorem RM : R3 (arrStep hArrs) 3 base3 161280 (Tn ONK3N) parN labN
    (fun h j => posF (nrec ONK3N h) j) :=
  R3_congr (node_replay hN hS) fun i hi j hj => step_eq hj hi

theorem mTree_eq : mTree = (Array.ofFn (n := 161280) fun i => parN i.val,
    Array.ofFn (n := 161280) fun i => labN i.val, Array.ofFn (n := 161280) fun i => Tn ONK3N i.val) :=
  bfs3_replay RM le_rfl

theorem mPar_eq : mPar = Array.ofFn (n := 161280) fun i => parN i.val := by
  unfold mPar
  rw [mTree_eq]

theorem mLab_eq : mLab = Array.ofFn (n := 161280) fun i => labN i.val := by
  unfold mLab
  rw [mTree_eq]

theorem mIm_eq : mIm = Array.ofFn (n := 161280) fun i => Tn ONK3N i.val := by
  unfold mIm
  rw [mTree_eq]

theorem mPar_get {k : Nat} (hk : k < 161280) : mPar[k]! = parN k := by
  rw [mPar_eq, ofFn_get3 hk]

theorem mLab_get {k : Nat} (hk : k < 161280) : mLab[k]! = labN k := by
  rw [mLab_eq, ofFn_get3 hk]

theorem mIm_get {k : Nat} (hk : k < 161280) : mIm[k]! = Tn ONK3N k := by
  rw [mIm_eq, ofFn_get3 hk]

theorem mIm_size : mIm.size = 161280 := by
  rw [mIm_eq, Array.size_ofFn]

theorem m_tree : treeOK 161280 3 (arrStep hArrs) base3 mPar mLab mIm = true := by
  have := treeOK_of_R3 RM
  rw [← mPar_eq, ← mLab_eq, ← mIm_eq] at this
  exact this

theorem m_distinct : distinctOK 161280 mIm = true := by
  refine distinctOK_of_inj mIm_size fun a ha b hb e => ?_
  rw [mIm_size] at ha hb
  rw [mIm_get ha, mIm_get hb] at e
  exact RM.inj a ha b hb e

theorem m_par_lt : ∀ k < 161280, k ≠ 0 → mPar[k]! < k ∧ mLab[k]! < 3 := by
  intro k hk h0
  rw [mPar_get hk, mLab_get hk]
  exact ⟨(RM.tree k (Nat.pos_of_ne_zero h0) hk).1, (RM.tree k (Nat.pos_of_ne_zero h0) hk).2.1⟩

theorem m_sim : treeOK 161280 3 (arrStep vArrs) base3 mPar mLab mSim = true :=
  treeOK_treeTriples (by decide) m_par_lt

theorem sig_lt' {k : Nat} (hk : k < 161280) : sigF (nrec ONK3N k) < 161280 :=
  sig_lt hN hU k hk

theorem base3_eq : base3 = Tn ONK3N 0 :=
  (BK_triple ((nodes_of hN (k := 0) (by decide)).root rfl).1).symm

theorem mSim_get : ∀ k < 161280, mSim[k]! = Tn ONK3N (sigF (nrec ONK3N k)) := by
  obtain ⟨-, h0, hs⟩ := treeTriples_get (step := arrStep vArrs) (start := base3) (par := mPar)
    (lab := mLab) (n := 161280) (by decide)
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases e : k = 0
    · subst e
      change (treeTriples (arrStep vArrs) base3 mPar mLab 161280)[0]! = _
      rw [h0, ((nodes_of hN (k := 0) (by decide)).root rfl).2.2.2.1]
      exact base3_eq
    · obtain ⟨t1, t2, -, -, -, t6⟩ := (nodes_of hN hk).tree e
      have hq : parN k < 161280 := Nat.lt_trans t1 hk
      have hp := m_par_lt k hk e
      change (treeTriples (arrStep vArrs) base3 mPar mLab 161280)[k]! = _
      rw [hs k (Nat.pos_of_ne_zero e) hk hp.1]
      change arrStep vArrs mLab[k]! mSim[mPar[k]!]! = _
      rw [mPar_get hk, mLab_get hk, ih _ t1 hq]
      have hsq := sig_lt' hq
      obtain ⟨a, b, c⟩ := node_lt hsq
      obtain ⟨-, hw⟩ := walk_map hN _ _ (hU _ t2) _ hsq
      rw [t6, ← hw]
      unfold arrStep map3 Tn
      dsimp only
      rw [vArrs_get (labN k) t2 _ a, vArrs_get (labN k) t2 _ b, vArrs_get (labN k) t2 _ c]

theorem Tn_inj {a b : Nat} (ha : a < 161280) (hb : b < 161280) :
    Tn ONK3N a = Tn ONK3N b ↔ a = b :=
  ⟨RM.inj a ha b hb, fun e => by rw [e]⟩

theorem tTest_eq {k : Nat} (hk : k < 161280) : tTest k = decide (tVal ONK3N k = 1) := by
  unfold tTest
  have hw := wrd_lt hN k hk
  have hwm := walk_map hN _ _ hw.2 _ (sig_lt' hk)
  rw [mSim_get k hk, pathEval_map hN (fun l hl x hx => (hArrs_get hl hx).1)
    (fun k hk => mPar_get hk) (fun k hk => mLab_get hk) k hk _ (sig_lt' hk), base3_eq]
  unfold tVal
  rw [sN]
  generalize walk ONK3N (depF (nrec ONK3N k)) (wrdF (nrec ONK3N k)) (sigF (nrec ONK3N k)) = W at hwm ⊢
  by_cases e : W = 0
  · subst e
    simp
  · have h1 : (Tn ONK3N W == Tn ONK3N 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      exact e ((Tn_inj hwm.1 (by decide)).1 h)
    rw [h1, beqF e]
    rfl

theorem sumBlk_zero (b : Nat) (f : Nat → Nat) : sumBlk b f 0 = 0 := rfl

theorem sumBlk_succ' (b : Nat) (f : Nat → Nat) (n : Nat) :
    sumBlk b f (n + 1) = f (b + n) + sumBlk b f n := rfl

theorem sumBlk_add (b : Nat) (f : Nat → Nat) (m n : Nat) :
    sumBlk b f (m + n) = sumBlk b f m + sumBlk (b + m) f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, sumBlk_succ', sumBlk_succ', ih, Nat.add_assoc b m n]
    omega

theorem sumBlk_congr {b : Nat} {f g : Nat → Nat} {n : Nat} (h : ∀ l < n, f (b + l) = g (b + l)) :
    sumBlk b f n = sumBlk b g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBlk_succ', sumBlk_succ', ih fun l hl => h l (Nat.lt_succ_of_lt hl), h n (Nat.lt_succ_self n)]

theorem sumBlk_slices (f : Nat → Nat) (s : Nat) :
    sumBlk 0 f (512 * s) = sumBlk 0 (fun t => sumBlk (512 * t) f 512) s := by
  induction s with
  | zero => rw [Nat.mul_zero, sumBlk_zero, sumBlk_zero]
  | succ s ih =>
    rw [Nat.mul_succ, sumBlk_add, ih, sumBlk_succ' 0 (fun t => sumBlk (512 * t) f 512) s]
    simp only [Nat.zero_add]
    omega

theorem filter_len (p : Nat → Bool) (n : Nat) :
    ((List.range n).filter p).length = sumBlk 0 (fun k => if p k = true then 1 else 0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, sumBlk_succ', Nat.zero_add]
    cases h : p n <;> simp [h, List.filter_cons, Nat.add_comm]

theorem tVal_le (k : Nat) : tVal ONK3N k = 0 ∨ tVal ONK3N k = 1 := by
  unfold tVal
  rw [sN]
  generalize Nat.beq _ _ = c
  cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem tcSum : Nat.beq (sumBlk 0 TC 315) 1344 = true := by quickRfl

theorem tList_len : tList.length ≤ 1344 := by
  unfold tList
  rw [filter_len]
  have e1 : sumBlk 0 (fun k => if tTest k = true then 1 else 0) 161280 =
      sumBlk 0 (tVal ONK3N) 161280 := by
    refine sumBlk_congr fun l hl => ?_
    rw [Nat.zero_add, tTest_eq hl]
    rcases tVal_le l with h | h <;> simp [h]
  have e2 : sumBlk 0 (tVal ONK3N) (512 * 315) = sumBlk 0 TC 315 := by
    rw [sumBlk_slices]
    refine sumBlk_congr fun l hl => ?_
    rw [Nat.zero_add, Nat.mul_comm]
    exact counts_of hN hl
  have e3 : sumBlk 0 TC 315 = 1344 := beqT tcSum
  rw [e1]
  exact Nat.le_of_eq (e2.trans e3)

end CertificateChecks.KernelSpor.ONK3

end
