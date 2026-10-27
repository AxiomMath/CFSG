
module

public import Certificates.Kernel.Sporadic.SuzK.Act
public import CFSG.Certificates.Kernel.Spor.TBfsSound
public import CFSG.Certificates.Kernel.Spor.F3LaneSepSound
import Certificates.Kernel.Sporadic.SuzK.TR0
import Certificates.Kernel.Sporadic.SuzK.TR1
import Certificates.Kernel.Sporadic.SuzK.Misc
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Suz.CertificateBase

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzK.trAll CertificateChecks.KernelSpor.SuzK.trSl 50
#kon_join CertificateChecks.KernelSpor.SuzK.hdAll CertificateChecks.KernelSpor.SuzK.hdAt 7

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.TW CFSG.KS.F3L
  CFSG.KS.F3R CFSG.F3.Native CFSG.Sporadic.Suz.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem trA (s : Nat) (hs : s < 50) : trSl s = true := trAll s hs

theorem hdA (i : Nat) (hi : i < 7) : hdAt i = true := hdAll i hi

theorem sl_spec {n cnt r lo len : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (h : tbfsSlK n cnt r L LV PTS POS PAR LAB TI lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < cnt → tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  intro k h1 h2 h3
  have h' := Raw.Orb.allN_iff.1 h (k - lo) (by omega)
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr h3)] at h'
  exact h'

theorem pt_of {i c : Nat} (h : treeSl i c = true) : ∀ k, 1000 * c ≤ k → k < 1000 * c + 1000 →
    k < TCNT i → tbfsPtK 22880 (TCNT i) (lvK LJ BJ 28 (TLV i)).length LJ (lvAt LJ BJ 28 (TLV i))
      (TPTS i) (TPOS i) (TPAR i) (TLAB i) (TTI i) k = true := by
  intro k h1 h2 h3
  unfold treeSl at h
  exact sl_spec h k (by change c * 1000 ≤ k; omega) (by change k < c * 1000 + 1000; omega) h3

theorem blt_f {a b : Nat} (h : b ≤ a) : (Nat.blt a b = true) = False := by
  rw [Nat.blt_eq]
  exact propext ⟨fun h' => absurd h' (by omega), False.elim⟩

theorem beq_f {a b : Nat} (h : a ≠ b) : (Nat.beq a b = true) = False := by
  rw [Nat.beq_eq]
  exact propext ⟨fun h' => absurd h' h, False.elim⟩

theorem trSl_spec {s : Nat} (h : trSl s = true) :
    (s < 23 → treeSl 0 s = true) ∧ (23 ≤ s → s < 32 → treeSl 1 (s - 23) = true) ∧
    (s = 32 → treeSl 2 0 = true) ∧ (s = 33 → treeSl 3 0 = true) ∧
    (34 ≤ s → s < 48 → treeSl 4 (s - 34) = true) ∧ (s = 48 → treeSl 5 0 = true) ∧
    (49 ≤ s → treeSl 6 0 = true) := by
  unfold trSl at h
  simp only [Raw.Orb.bIf_eq] at h
  refine ⟨fun h0 => ?_, fun h0 h1 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 h1 => ?_, fun h0 => ?_,
    fun h0 => ?_⟩
  · rwa [if_pos (Nat.blt_eq.mpr h0)] at h
  · rwa [if_neg (by rw [blt_f h0]; exact id), if_pos (Nat.blt_eq.mpr h1)] at h
  · subst h0
    exact h
  · subst h0
    exact h
  · rwa [if_neg (by rw [blt_f (by omega)]; exact id), if_neg (by rw [blt_f (by omega)]; exact id),
      if_neg (by rw [beq_f (by omega)]; exact id), if_neg (by rw [beq_f (by omega)]; exact id),
      if_pos (Nat.blt_eq.mpr h1)] at h
  · subst h0
    exact h
  · rwa [if_neg (by rw [blt_f (by omega)]; exact id), if_neg (by rw [blt_f (by omega)]; exact id),
      if_neg (by rw [beq_f (by omega)]; exact id), if_neg (by rw [beq_f (by omega)]; exact id),
      if_neg (by rw [blt_f (by omega)]; exact id), if_neg (by rw [beq_f (by omega)]; exact id)] at h

theorem tcnt : TCNT 0 = 22880 ∧ TCNT 1 = 8505 ∧ TCNT 2 = 144 ∧ TCNT 3 = 16 ∧ TCNT 4 = 13608 ∧
    TCNT 5 = 280 ∧ TCNT 6 = 486 := by
  decide +kernel

theorem tree_pts {i : Nat} (hi : i < 7) : ∀ k < TCNT i, tbfsPtK 22880 (TCNT i)
    (lvK LJ BJ 28 (TLV i)).length LJ (lvAt LJ BJ 28 (TLV i)) (TPTS i) (TPOS i) (TPAR i)
      (TLAB i) (TTI i) k = true := by
  intro k hk
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := tcnt
  interval_cases i
  · rw [c0] at hk
    exact pt_of ((trSl_spec (trA (k / 1000) (by omega))).1 (by omega)) k (by omega) (by omega)
      (by rw [c0]; exact hk)
  · rw [c1] at hk
    have h := (trSl_spec (trA (23 + k / 1000) (by omega))).2.1 (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at h
    exact pt_of h k (by omega) (by omega) (by rw [c1]; exact hk)
  · rw [c2] at hk
    exact pt_of ((trSl_spec (trA 32 (by norm_num))).2.2.1 rfl) k (by omega) (by omega)
      (by rw [c2]; exact hk)
  · rw [c3] at hk
    exact pt_of ((trSl_spec (trA 33 (by norm_num))).2.2.2.1 rfl) k (by omega) (by omega)
      (by rw [c3]; exact hk)
  · rw [c4] at hk
    have h := (trSl_spec (trA (34 + k / 1000) (by omega))).2.2.2.2.1 (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at h
    exact pt_of h k (by omega) (by omega) (by rw [c4]; exact hk)
  · rw [c5] at hk
    exact pt_of ((trSl_spec (trA 48 (by norm_num))).2.2.2.2.2.1 rfl) k (by omega) (by omega)
      (by rw [c5]; exact hk)
  · rw [c6] at hk
    exact pt_of ((trSl_spec (trA 49 (by norm_num))).2.2.2.2.2.2 (by omega)) k (by omega) (by omega)
      (by rw [c6]; exact hk)

theorem invK_ok : invK LJ 22880 28 = true := by
  unfold invK
  rw [Raw.Orb.allN_iff]
  intro j hj
  change j < 14 at hj
  have h := invAll j hj
  unfold invSl at h
  exact h

theorem tree_spec {i : Nat} (hi : i < 4) :
    tbfsHdK 22880 (BJ i) (TCNT i) (TPTS i) (TPOS i) (TPAR i) (TLAB i) = true ∧
      ∀ k < TCNT i, tbfsPtK 22880 (TCNT i) (lvK LJ BJ 28 i).length LJ (lvAt LJ BJ 28 i) (TPTS i)
        (TPOS i) (TPAR i) (TLAB i) (TTI i) k = true := by
  have hl : TLV i = i := by interval_cases i <;> rfl
  have hr : TROOT i = BJ i := by interval_cases i <;> rfl
  have hh := hdA i (by omega)
  unfold hdAt at hh
  rw [hr] at hh
  refine ⟨hh, fun k hk => ?_⟩
  have := tree_pts (i := i) (by omega) k hk
  rw [hl] at this
  exact this

theorem chain_hyp : ChainHyp 22880 28 4 (chainLetters orbLit) chainBase chainQ (chainQb ()) LJ BJ
    [0, 1, 2, 3, 4, 5] BJ TCNT TPTS TPOS TPAR TLAB TTI where
  letters := ⟨letters_TR.1, fun l hl x hx => (letters_TR.2 l hl x hx).1⟩
  inv := ⟨rfl, invK_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem prod_cnt : ((List.range 4).map TCNT).prod = 448345497600 := by
  decide +kernel

theorem chain_eq : chainTrees 22880 (chainLetters orbLit) chainBase =
      Array.ofFn (n := 4) (fun i => tbfsRec 22880 (TCNT i.val) (TPTS i.val) (TPOS i.val)
        (TPAR i.val) (TLAB i.val)) ∧
    ∀ chunks, chainOK 22880 (chainLetters orbLit) chainBase chainQ (chainQb ())
      (chainTrees 22880 (chainLetters orbLit) chainBase) chunks = true :=
  pchain_of_card chain_hyp (letters_card.trans (le_of_eq prod_cnt.symm))

theorem lv1_eq : levelLetters (chainLetters orbLit) chainBase 1 = (lvK LJ BJ 28 1).toArray :=
  levelLetters_eq chain_hyp 1 (by norm_num)

theorem sub_eq {i : Nat} (hi4 : 4 ≤ i) (hi : i < 7) :
    treeBFS 22880 (TROOT i) (chainLetters orbLit) (levelLetters (chainLetters orbLit) chainBase 1) =
        tbfsRec 22880 (TCNT i) (TPTS i) (TPOS i) (TPAR i) (TLAB i) ∧
    treeOK 22880 (TROOT i) (tbfsRec 22880 (TCNT i) (TPTS i) (TPOS i) (TPAR i) (TLAB i))
      (chainLetters orbLit) (levelLetters (chainLetters orbLit) chainBase 1) = true := by
  rw [lv1_eq]
  have hh := hdA i hi
  unfold hdAt at hh
  have hp := tree_pts (i := i) hi
  have hl : TLV i = 1 := by interval_cases i <;> rfl
  rw [hl] at hp
  refine tbfsK_sound (L := LJ) (LV := lvAt LJ BJ 28 1) (TI := TTI i) ⟨by simp, fun t ht => ?_⟩ hh hp
  have ht' : t < (lvK LJ BJ 28 1).length := by simpa using ht
  have hm := List.getElem_mem ht'
  have hlt : (lvK LJ BJ 28 1)[t] < 28 := by
    unfold lvK at hm
    exact List.mem_range.1 (List.mem_filter.1 hm).1
  have e : (lvK LJ BJ 28 1).toArray[t]! = lvAt LJ BJ 28 1 t := by
    rw [getElem!_pos _ t (by simpa using ht')]
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e]
  have e2 : lvAt LJ BJ 28 1 t = (lvK LJ BJ 28 1)[t] := by
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e2]
  exact ⟨rfl, by rw [letters_TR.1]; exact hlt, fun x hx => (letters_TR.2 _ hlt x hx).1⟩

theorem inT_eq {i p : Nat} (hp : p < 22880) :
    inT (tbfsRec 22880 (TCNT i) (TPTS i) (TPOS i) (TPAR i) (TLAB i)) p = inTK i p := by
  have hpos := pos_ap (n := 22880) (CNT := TCNT) (PTS := TPTS) (POS := TPOS) (PAR := TPAR)
    (LAB := TLAB) (i := i) hp
  have hs := pts_size (n := 22880) (CNT := TCNT) (PTS := TPTS) (POS := TPOS) (PAR := TPAR)
    (LAB := TLAB) i
  unfold trK at hpos hs
  unfold inT inTK
  rw [hpos, hs, Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq]
  by_cases hq : r32 (TPOS i) p < TCNT i
  · have hpts := pts_ap (n := 22880) (CNT := TCNT) (PTS := TPTS) (POS := TPOS) (PAR := TPAR)
      (LAB := TLAB) (i := i) hq
    unfold trK at hpts
    rw [hpts]
    have e1 : (r32 (TPOS i) p).blt (TCNT i) = true := Nat.blt_eq.mpr hq
    rw [e1, decide_eq_true hq, Bool.true_and, Bool.true_and]
    rfl
  · simp [hq, Nat.blt_eq]

theorem cover_pt {p : Nat} (hp : p < 22880) :
    (p == 0 || inT (tbfsRec 22880 (TCNT 1) (TPTS 1) (TPOS 1) (TPAR 1) (TLAB 1)) p ||
      inT (tbfsRec 22880 (TCNT 4) (TPTS 4) (TPOS 4) (TPAR 4) (TLAB 4)) p ||
      inT (tbfsRec 22880 (TCNT 5) (TPTS 5) (TPOS 5) (TPAR 5) (TLAB 5)) p ||
      inT (tbfsRec 22880 (TCNT 6) (TPTS 6) (TPOS 6) (TPAR 6) (TLAB 6)) p) = true := by
  have h := Raw.Orb.allN_iff.1 cover_ok p hp
  rw [inT_eq hp, inT_eq hp, inT_eq hp, inT_eq hp]
  simp only [Raw.Orb.bIf_eq] at h
  by_cases h0 : p = 0
  · subst h0
    rfl
  rw [if_neg (by rw [beq_f h0]; exact id)] at h
  simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or]
  by_cases h1 : inTK 1 p = true
  · exact Or.inl (Or.inl (Or.inl h1))
  rw [if_neg h1] at h
  by_cases h4 : inTK 4 p = true
  · exact Or.inl (Or.inl (Or.inr h4))
  rw [if_neg h4] at h
  by_cases h5 : inTK 5 p = true
  · exact Or.inl (Or.inr h5)
  rw [if_neg h5] at h
  exact Or.inr h

theorem sep_mats : sepIdx.map (fun r => toVM orbLit.keys[r]!) = (LsS.map (unlane 64)).toArray := by
  have hq : sepIdx = #[0, 1, 2, 3, 4, 5] := rfl
  rw [hq]
  simp only [List.map_toArray, List.map_cons, List.map_nil, LsS]
  rw [keys_get (k := 0) (by norm_num), keys_get (k := 1) (by norm_num),
    keys_get (k := 2) (by norm_num), keys_get (k := 3) (by norm_num),
    keys_get (k := 4) (by norm_num), keys_get (k := 5) (by norm_num),
    toVM_keyW, toVM_keyW, toVM_keyW, toVM_keyW, toVM_keyW, toVM_keyW]

theorem LsS_wf : ∀ L ∈ LsS, L.wf = true := by
  intro L hL
  simp only [LsS, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl
  · exact laneK_canon (by norm_num)
  · exact laneK_canon (by norm_num)
  · exact laneK_canon (by norm_num)
  · exact laneK_canon (by norm_num)
  · exact laneK_canon (by norm_num)
  · exact laneK_canon (by norm_num)

set_option Elab.async false

theorem wl_wf : WL.wf = true := by decide +kernel

theorem vec_lt : (sepVec ()).p < 2 ^ 64 ∧ (sepVec ()).m < 2 ^ 64 := by decide

theorem sepK_ok : sepOK 64 (LsS.map (unlane 64)).toArray sepTerms (sepVec ()) (sepK ()) (sepP ())
    (sepTinv ()) sepTree = true := by
  have hd : 0 < 64 := by norm_num
  unfold sepOK
  rw [combM_unlane hd idM_eq LsS sepTerms (by decide), spinVecs_lane hd LsS_wf vec_lt.1 vec_lt.2
    sepTree (by decide)]
  change (_ && (mulVecM 64 (unlane 64 WL) (sepVec ())).isZero && _ && _ && _ && _ && _) = true
  rw [mulVec_unlane hd wl_wf vec_lt.1 vec_lt.2]
  simp only [mul_eq, eqM_eq, wfM_eq, ← Array.all_toList]
  decide +kernel

theorem sep_ok : sepOK 64 (sepIdx.map fun r => toVM orbLit.keys[r]!) sepTerms (sepVec ()) (sepK ())
    (sepP ()) (sepTinv ()) sepTree = true := by
  rw [sep_mats]
  exact sepK_ok

theorem subRoots_eq : subRoots[0]! = TROOT 4 ∧ subRoots[1]! = TROOT 5 ∧ subRoots[2]! = TROOT 6 :=
  ⟨rfl, rfl, rfl⟩

theorem action_ok (chunks : Nat) : actionChecks orbLit chunks = true := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := tcnt
  have hce := chain_eq.1
  unfold actionChecks
  dsimp only
  rw [subRoots_eq.1, subRoots_eq.2.1, subRoots_eq.2.2,
    (sub_eq (i := 4) (by norm_num) (by norm_num)).1, (sub_eq (i := 5) (by norm_num) (by norm_num)).1,
    (sub_eq (i := 6) (by norm_num) (by norm_num)).1]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨keys_size, alpha_TR.1⟩, beta_TR.1⟩, ?_⟩, sep_ok⟩, ?_⟩,
    chain_eq.2 chunks⟩, ?_⟩, (sub_eq (i := 4) (by norm_num) (by norm_num)).2⟩, ?_⟩,
    (sub_eq (i := 5) (by norm_num) (by norm_num)).2⟩, ?_⟩,
    (sub_eq (i := 6) (by norm_num) (by norm_num)).2⟩, ?_⟩, ?_⟩
  · exact invOK_of beta_TR binv_TR fun i hi => beta_ord hi
  · rw [← Array.all_toList]
    decide
  · rw [hce]
    simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
      List.map_nil, Array.size_ofFn]
    decide +kernel
  · simp only [tbfsRec, Array.size_ofFn, c4]
  · simp only [tbfsRec, Array.size_ofFn, c5]
  · simp only [tbfsRec, Array.size_ofFn, c6]
  · rw [hce, TW.allIn_iff]
    intro p hp
    have e : (Array.ofFn (n := 4) fun i => tbfsRec 22880 (TCNT i.val) (TPTS i.val) (TPOS i.val)
        (TPAR i.val) (TLAB i.val))[1]! = tbfsRec 22880 (TCNT 1) (TPTS 1) (TPOS 1) (TPAR 1) (TLAB 1) := by
      rw [getElem!_pos _ 1 (by simp), Array.getElem_ofFn]
    rw [e]
    exact cover_pt hp

end CertificateChecks.KernelSpor.SuzK

end
