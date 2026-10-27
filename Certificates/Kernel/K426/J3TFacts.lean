module

public import Certificates.Kernel.K426.J3TK
public import Certificates.Kernel.SporSch.J3K426.Sift
public import CFSG.Certificates.Kernel.HeLoc.TreeSound
public import CFSG.Certificates.Kernel.HeLoc.PTailSound
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK426J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne
open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch
open scoped commutatorElement

noncomputable abbrev GJ : Subgroup (Equiv.Perm (Fin 6156)) := Gen 6156 j3StrongArrs 2

theorem unpackGet {p x : Nat} (hx : x < 6156) :
    (unpack 6156 13 p)[x]! = pg 13 (mask 13) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem repF_of_rep {p : Nat} {u : Equiv.Perm (Fin 6156)} (h : Rep 6156 (unpack 6156 13 p) u) :
    RepF 6156 (pg 13 (mask 13) p) u := fun x hx => by
  rw [← unpackGet hx]
  exact h ⟨x, hx⟩

@[expose] noncomputable def gp (k : Nat) : Equiv.Perm (Fin 6156) :=
  permOfArr 6156 (unpack 6156 13 (F k))

theorem inv_k {k : Nat} (hk : k < 40) :
    invCand 6156 (unpack 6156 13 (F k)) = unpack 6156 13 (FI k) ∧
      isInvA 6156 (unpack 6156 13 (F k)) (unpack 6156 13 (FI k)) = true :=
  invEqK_sound (Orb.allN_iff.1 kPerm k hk)

theorem rep_gp {k : Nat} (hk : k < 40) : Rep 6156 (unpack 6156 13 (F k)) (gp k) :=
  (rep_permOfArr (inv_k hk).2).1

theorem rep_gpi {k : Nat} (hk : k < 40) : Rep 6156 (unpack 6156 13 (FI k)) (gp k)⁻¹ :=
  (rep_permOfArr (inv_k hk).2).2

theorem valid_k {k : Nat} (hk : k < 40) : validA 6156 (unpack 6156 13 (F k)) = true := by
  unfold validA
  rw [(inv_k hk).1]
  exact (inv_k hk).2

theorem hg {k : Nat} (hk : k < 40) : RepF 6156 (g k) (gp k) := repF_of_rep (rep_gp hk)

theorem hgi {k : Nat} (hk : k < 40) : RepF 6156 (gi k) (gp k)⁻¹ := repF_of_rep (rep_gpi hk)

theorem arr_k {k : Nat} (hk : k < 40) : j3tArr k = unpack 6156 13 (F k) := J3KT.arr hk

theorem word_k {k : Nat} (hk : k < 40) :
    wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (WS.getD k []) (F k) = true := by
  rcases Nat.lt_or_ge k 10 with h0 | h0
  · exact Orb.allN_iff.1 kW0 k h0
  rcases Nat.lt_or_ge k 20 with h1 | h1
  · have := Orb.allN_iff.1 kW1 (k - 10) (by omega)
    rwa [show Nat.add 10 (k - 10) = k by simp only [Nat.add_eq]; omega] at this
  rcases Nat.lt_or_ge k 30 with h2 | h2
  · have := Orb.allN_iff.1 kW2 (k - 20) (by omega)
    rwa [show Nat.add 20 (k - 20) = k by simp only [Nat.add_eq]; omega] at this
  · have := Orb.allN_iff.1 kW3 (k - 30) (by omega)
    rwa [show Nat.add 30 (k - 30) = k by simp only [Nat.add_eq]; omega] at this

theorem sift_k {k : Nat} (hk : k < 40) :
    siftA 6156 PairJ3.levels PairJ3.baseArr 0 (unpack 6156 13 (F k)) = true :=
  J3KT.sift_of (word_k hk)

theorem gen_le : Subgroup.closure (Set.range fun j : Fin 5 => permOfArr 6156 j3StrongArrs[j.val]!) ≤
    GJ := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact S_mem_Gen J3KT.hd j.val (by simpa [j3StrongArrs] using j.2)

theorem gp_mem {k : Nat} (hk : k < 40) : gp k ∈ GJ := by
  have hS : j3StrongArrs.size = 5 := PJ3Check.binds.2.2.2.1
  obtain ⟨hw, hl⟩ := wordEqK_sound ⟨hS, PJ3Check.binds.2.2.2.2.1⟩ PJ3Check.perm (word_k hk)
  have hrep := rep_wordA (n := 6156) (j := 5) (gs := fun h => permOfArr 6156 j3StrongArrs[h]!)
    (fun h hh => rep_S J3KT.hd (by omega)) (fun h hh => rep_Si J3KT.hd (by omega)) _ hl
  rw [hw] at hrep
  rw [(rep_gp hk).unique hrep]
  exact gen_le (Quiver.SchreierGraph.evalWord_mem_closure _ _)

theorem bs_lt : ∀ b ∈ bs, b < 6156 := by decide

theorem eq_of_base {x y : Equiv.Perm (Fin 6156)} (hx : x ∈ GJ) (hy : y ∈ GJ)
    (h : ∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) : x = y := by
  have hm : y⁻¹ * x ∈ Fix 6156 j3StrongArrs 2 PairJ3.baseArr PairJ3.baseArr.size := by
    refine ⟨GJ.mul_mem (GJ.inv_mem hy) hx, fun t ht hb => ?_⟩
    have hbt : PairJ3.baseArr[t]! ∈ bs := by
      have : t < 4 := ht
      interval_cases t <;> decide
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (h _ hbt)
  exact (inv_mul_eq_one.1 (fix_one J3KT.hd PJ3Check.card_le hm)).symm

theorem eqOnL_symm {l : List Nat} {f f' : Nat → Nat} (h : eqOnL l f f' = true) :
    eqOnL l f' f = true :=
  (eqOnL_iff _ _ _).2 fun b hb => ((eqOnL_iff _ _ _).1 h b hb).symm

theorem eqA_eq {a b : Array Nat} {A B : Equiv.Perm (Fin 6156)} {f f' : Nat → Nat}
    (ha : Rep 6156 a A) (hb : Rep 6156 b B) (hA : A ∈ GJ) (hB : B ∈ GJ) (hf : RepF 6156 f A)
    (hf' : RepF 6156 f' B) : eqA 6156 a b = eqOnL bs f f' := by
  apply Bool.eq_iff_iff.2
  rw [eqA_iff ha hb, eqOnL_iff]
  constructor
  · rintro rfl c hc
    rw [hf c (bs_lt c hc), hf' c (bs_lt c hc)]
  · intro h
    refine eq_of_base hA hB fun c hc => ?_
    rw [← hf c (bs_lt c hc), ← hf' c (bs_lt c hc)]
    exact h c hc

theorem nQ : TQ.N = 243 := Nat.eq_of_beq_eq_true kNQ
theorem nA : TA.N = 1080 := Nat.eq_of_beq_eq_true kNA
theorem nD : TD.N = 360 := Nat.eq_of_beq_eq_true kND

@[expose] noncomputable def gpq (k : Nat) : Equiv.Perm (Fin 6156) := gp k
@[expose] noncomputable def gpa (k : Nat) : Equiv.Perm (Fin 6156) := gp (33 + k)
@[expose] noncomputable def gpd (k : Nat) : Equiv.Perm (Fin 6156) := gp (37 + k)

theorem ofFn_get {m c j : Nat} (hj : j < m) :
    (Array.ofFn fun i : Fin m => j3tArr (c + i.val))[j]! = j3tArr (c + j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem hgsQ : ∀ k < 5, Rep 6156 j3tCBGens[k]! (gpq k) := fun k hk => by
  rw [j3tCBGens, ofFn_get hk, arr_k (by omega), Nat.zero_add]
  exact rep_gp (by omega)

theorem hgsA : ∀ k < 4, Rep 6156 j3tCAGens[k]! (gpa k) := fun k hk => by
  rw [j3tCAGens, ofFn_get hk, arr_k (by omega)]
  exact rep_gp (by omega)

theorem hgsD : ∀ k < 2, Rep 6156 j3tDGens[k]! (gpd k) := fun k hk => by
  rw [j3tDGens, ofFn_get hk, arr_k (by omega)]
  exact rep_gp (by omega)

theorem hgQ : ∀ k < 5, RepF 6156 (gq k) (gpq k) := fun k hk => hg (by omega)

theorem hgA : ∀ k < 4, RepF 6156 (ga k) (gpa k) := fun k hk => by
  have := hg (k := 33 + k) (by omega)
  exact this

theorem hgD : ∀ k < 2, RepF 6156 (gd k) (gpd k) := fun k hk => by
  have := hg (k := 37 + k) (by omega)
  exact this

theorem treeQ : TreeOK 5 243 TQ.P TQ.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeQ i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem treeA : TreeOK 4 1080 TA.P TA.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeA i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem treeD : TreeOK 2 360 TD.P TD.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeD i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem hmul : ∀ a ∈ GJ, ∀ b ∈ GJ, (a * b ∈ GJ ↔ (a ∈ GJ ↔ b ∈ GJ)) :=
  fun a ha b hb => iff_of_true (GJ.mul_mem ha hb) (iff_of_true ha hb)

theorem hfaith : ∀ x ∈ GJ, ∀ y ∈ GJ, (x ∈ GJ ↔ y ∈ GJ) →
    (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y :=
  fun x hx y hy _ h => eq_of_base hx hy h

theorem q0_iff {gpk : Nat → Equiv.Perm (Fin 6156)} {m : Nat} (h : ∀ k < m, gpk k ∈ GJ) :
    ∀ k < m, (gpk k ∈ GJ ↔ q0 k = 0) := fun k hk => iff_of_true (h k hk) rfl

theorem q0_lt {m : Nat} : ∀ k < m, q0 k < 2 := fun _ _ => Nat.zero_lt_two

theorem memQ : ∀ k < 5, gpq k ∈ GJ := fun k hk => gp_mem (by omega)
theorem memA : ∀ k < 4, gpa k ∈ GJ := fun k hk => gp_mem (by omega)
theorem memD : ∀ k < 2, gpd k ∈ GJ := fun k hk => gp_mem (by omega)

theorem edgesQ : ∀ i < 243, ∀ k < 5, EQ i k < 243 ∧
    treeArr 6156 j3tCBGens TQ.P TQ.L (EQ i k) =
      compA 6156 j3tCBGens[k]! (treeArr 6156 j3tCBGens TQ.P TQ.L i) :=
  edges_of_edgeAtK treeQ hgQ hgsQ hmul memQ (q0_iff memQ) q0_lt bs_lt hfaith
    fun i hi => Orb.allN_iff.1 kEdgeQ i hi

theorem edgesA : ∀ i < 1080, ∀ k < 4, EA i k < 1080 ∧
    treeArr 6156 j3tCAGens TA.P TA.L (EA i k) =
      compA 6156 j3tCAGens[k]! (treeArr 6156 j3tCAGens TA.P TA.L i) :=
  edges_of_edgeAtK treeA hgA hgsA hmul memA (q0_iff memA) q0_lt bs_lt hfaith
    fun i hi => Orb.allN_iff.1 kEdgeA i hi

theorem edgesD : ∀ i < 360, ∀ k < 2, ED i k < 360 ∧
    treeArr 6156 j3tDGens TD.P TD.L (ED i k) =
      compA 6156 j3tDGens[k]! (treeArr 6156 j3tDGens TD.P TD.L i) :=
  edges_of_edgeAtK treeD hgD hgsD hmul memD (q0_iff memD) q0_lt bs_lt hfaith
    fun i hi => Orb.allN_iff.1 kEdgeD i hi

theorem keys_lt : ∀ p ∈ j3tKeys, p < 6156 := by decide

theorem keyQ : ∀ a < 243, ∀ b < 243, keyA 6156 j3tKeys (treeArr 6156 j3tCBGens TQ.P TQ.L a) =
    keyA 6156 j3tKeys (treeArr 6156 j3tCBGens TQ.P TQ.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := kq) fun j hj => Orb.allN_iff.1 kSortQ j hj
  intro a ha b hb e
  rw [keyA_treeArr treeQ hgQ hgsQ keys_lt ha, keyA_treeArr treeQ hgQ hgsQ keys_lt hb] at e
  exact hk a ha b hb e

theorem keyAk : ∀ a < 1080, ∀ b < 1080, keyA 6156 j3tKeys (treeArr 6156 j3tCAGens TA.P TA.L a) =
    keyA 6156 j3tKeys (treeArr 6156 j3tCAGens TA.P TA.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ka) fun j hj => Orb.allN_iff.1 kSortA j hj
  intro a ha b hb e
  rw [keyA_treeArr treeA hgA hgsA keys_lt ha, keyA_treeArr treeA hgA hgsA keys_lt hb] at e
  exact hk a ha b hb e

theorem keyD : ∀ a < 360, ∀ b < 360, keyA 6156 j3tKeys (treeArr 6156 j3tDGens TD.P TD.L a) =
    keyA 6156 j3tKeys (treeArr 6156 j3tDGens TD.P TD.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := kd) fun j hj => Orb.allN_iff.1 kSortD j hj
  intro a ha b hb e
  rw [keyA_treeArr treeD hgD hgsD keys_lt ha, keyA_treeArr treeD hgD hgsD keys_lt hb] at e
  exact hk a ha b hb e

theorem replayQ : CFSG.KC.Bfs.replayOK EQ 5 243 = true := kReplayQ
theorem replayA : CFSG.KC.Bfs.replayOK EA 4 1080 = true := kReplayA
theorem replayD : CFSG.KC.Bfs.replayOK ED 2 360 = true := kReplayD

theorem ptsQ : j3tCBCert.pts = Array.ofFn (n := 243) fun i => treeArr 6156 j3tCBGens TQ.P TQ.L i.val :=
  enumBfs_tree treeQ hgsQ (by simp [j3tCBGens]) (by norm_num) (by norm_num) keyQ edgesQ replayQ

theorem ptsA : j3tCACert.pts = Array.ofFn (n := 1080) fun i => treeArr 6156 j3tCAGens TA.P TA.L i.val :=
  enumBfs_tree treeA hgsA (by simp [j3tCAGens]) (by norm_num) (by norm_num) keyAk edgesA replayA

theorem ptsD : j3tDCert.pts = Array.ofFn (n := 360) fun i => treeArr 6156 j3tDGens TD.P TD.L i.val :=
  enumBfs_tree treeD hgsD (by simp [j3tDGens]) (by norm_num) (by norm_num) keyD edgesD replayD

theorem enumQ : enumOK 6156 j3tCBGens j3tKeys j3tCBCert = true :=
  enumOK_tree treeQ hgsQ (by simp [j3tCBGens]) (by norm_num) (by norm_num) keyQ edgesQ

theorem enumA : enumOK 6156 j3tCAGens j3tKeys j3tCACert = true :=
  enumOK_tree treeA hgsA (by simp [j3tCAGens]) (by norm_num) (by norm_num) keyAk edgesA

theorem enumD : enumOK 6156 j3tDGens j3tKeys j3tDCert = true :=
  enumOK_tree treeD hgsD (by simp [j3tDGens]) (by norm_num) (by norm_num) keyD edgesD

theorem getQ {k : Nat} (hk : k < 243) :
    j3tCBCert.pts[k]! = treeArr 6156 j3tCBGens TQ.P TQ.L k := by
  rw [ptsQ, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem getA {k : Nat} (hk : k < 1080) :
    j3tCACert.pts[k]! = treeArr 6156 j3tCAGens TA.P TA.L k := by
  rw [ptsA, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem getD {k : Nat} (hk : k < 360) :
    j3tDCert.pts[k]! = treeArr 6156 j3tDGens TD.P TD.L k := by
  rw [ptsD, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

@[expose] noncomputable def uq (i : Nat) : Equiv.Perm (Fin 6156) := treePerm gpq TQ.P TQ.L i
@[expose] noncomputable def ua (i : Nat) : Equiv.Perm (Fin 6156) := treePerm gpa TA.P TA.L i
@[expose] noncomputable def ud (i : Nat) : Equiv.Perm (Fin 6156) := treePerm gpd TD.P TD.L i

theorem repQ {k : Nat} (hk : k < 243) : Rep 6156 j3tCBCert.pts[k]! (uq k) := by
  rw [getQ hk]
  exact rep_treeArr treeQ hgsQ k hk

theorem repA {k : Nat} (hk : k < 1080) : Rep 6156 j3tCACert.pts[k]! (ua k) := by
  rw [getA hk]
  exact rep_treeArr treeA hgsA k hk

theorem repD {k : Nat} (hk : k < 360) : Rep 6156 j3tDCert.pts[k]! (ud k) := by
  rw [getD hk]
  exact rep_treeArr treeD hgsD k hk

theorem repFQ {k : Nat} (hk : k < 243) : RepF 6156 (tq k) (uq k) := repF_trV treeQ hgQ 243 k hk.le hk
theorem repFA {k : Nat} (hk : k < 1080) : RepF 6156 (ta k) (ua k) := repF_trV treeA hgA 1080 k hk.le hk
theorem repFD {k : Nat} (hk : k < 360) : RepF 6156 (td k) (ud k) := repF_trV treeD hgD 360 k hk.le hk

theorem memUQ {k : Nat} (hk : k < 243) : uq k ∈ GJ :=
  (trQ_spec treeQ hmul memQ (q0_iff memQ) q0_lt 243 k hk.le hk).1
theorem memUA {k : Nat} (hk : k < 1080) : ua k ∈ GJ :=
  (trQ_spec treeA hmul memA (q0_iff memA) q0_lt 1080 k hk.le hk).1
theorem memUD {k : Nat} (hk : k < 360) : ud k ∈ GJ :=
  (trQ_spec treeD hmul memD (q0_iff memD) q0_lt 360 k hk.le hk).1

theorem sizeQ : j3tCBCert.pts.size = 243 := by rw [ptsQ, Array.size_ofFn]
theorem sizeA : j3tCACert.pts.size = 1080 := by rw [ptsA, Array.size_ofFn]
theorem sizeD : j3tDCert.pts.size = 360 := by rw [ptsD, Array.size_ofFn]

theorem any_mem {c : ArrCert} {t : Array Nat} {k : Nat} (hk : k < c.pts.size)
    (h : eqA 6156 t c.pts[k]! = true) : c.pts.toList.any (eqA 6156 t) = true := by
  rw [List.any_eq_true]
  refine ⟨c.pts[k]!, ?_, h⟩
  rw [getElem!_pos c.pts k hk]
  exact Array.getElem_mem_toList _

theorem rep_id : RepF 6156 (fun x => x) (1 : Equiv.Perm (Fin 6156)) := RepF.one

theorem lines_get {j : Nat} (hj : j < 13) : j3tLines[j]! = unpack 6156 13 (F (5 + j)) := by
  rw [j3tLines, ofFn_get hj, arr_k (by omega)]

theorem reps_get {c : Nat} (hc : c < 2) : j3tReps[c]! = unpack 6156 13 (F (18 + c)) := by
  rw [j3tReps, ofFn_get hc, arr_k (by omega)]

theorem trans_get {j : Nat} (hj : j < 13) : j3tTrans[j]! = unpack 6156 13 (F (20 + j)) := by
  rw [j3tTrans, ofFn_get hj, arr_k (by omega)]

theorem g_get : j3tG = unpack 6156 13 (F 39) := by rw [j3tG, arr_k (by norm_num)]

theorem eqA_pow_id {a : Array Nat} {A : Equiv.Perm (Fin 6156)} {f : Nat → Nat}
    (ha : Rep 6156 a A) (hA : A ∈ GJ) (hf : RepF 6156 f A) (e : Nat) :
    eqA 6156 (powArr 6156 a e) (idA 6156) = eqOnL bs (powF f e) (fun x => x) :=
  eqA_eq (rep_powArr ha e) rep_idA (GJ.pow_mem hA e) GJ.one_mem (RepF.powF hf e) RepF.one

theorem anyR_congr {m : Nat} {f f' : Nat → Bool} (h : ∀ j < m, f j = f' j) :
    (List.range m).any f = (List.range m).any f' := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨j, hj, e⟩ => ⟨j, hj, (h j hj) ▸ e⟩, fun ⟨j, hj, e⟩ => ⟨j, hj, (h j hj).symm ▸ e⟩⟩

theorem bIf_cases {c t e : Bool} (h : bIf(c, t, e) = true) : (c = true ∧ t = true) ∨
    (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem lines_ok : linesOK3 3 243 13 6156 j3tCBGens j3tKeys j3tCBCert j3tLines = true := by
  unfold linesOK3
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨enumQ, sizeQ⟩, fun k hk => ?_⟩, fun j hj => ?_⟩
  · have hr := repQ hk
    have hf := repFQ hk
    have hm := memUQ hk
    have hL : ∀ j < 13, ∀ e < 3, eqA 6156 j3tCBCert.pts[k]! (powArr 6156 j3tLines[j]! e) =
        eqOnL bs (tq k) (powF (g (Nat.add 5 j)) e) := fun j hj e _ => by
      rw [lines_get hj]
      exact eqA_eq hr (rep_powArr (rep_gp (k := 5 + j) (by omega)) e) hm
        (GJ.pow_mem (gp_mem (k := 5 + j) (by omega)) e) hf (RepF.powF (hg (k := 5 + j) (by omega)) e)
    rw [eqA_pow_id hr hm hf 3, eqA_eq hr rep_idA hm GJ.one_mem hf RepF.one,
      anyR_congr fun j hj => anyR_congr fun e he => hL j hj e he]
    have hl := Orb.allN_iff.1 kLines k hk
    unfold lineAt at hl
    rcases bIf_cases hl with ⟨h1, h2⟩ | ⟨h1, -⟩
    · rw [h1]
      rcases bIf_cases h2 with ⟨h3, -⟩ | ⟨h3, h4⟩
      · rw [h3]
        rfl
      · rw [h3, ← CFSG.KC.Misc.ArrEnum.anyNP_eq]
        simp only [← CFSG.KC.Misc.ArrEnum.anyNP_eq]
        rw [h4]
        rfl
    · rw [h1]
      rfl
  · rw [lines_get hj, valid_k (by omega)]
    refine ⟨rfl, ?_⟩
    rw [eqA_pow_id (rep_gp (k := 5 + j) (by omega)) (gp_mem (k := 5 + j) (by omega))
      (hg (k := 5 + j) (by omega)) 3]
    exact Orb.allN_iff.1 kCubes.1 j hj

theorem reps_ok : allLt 2 (fun c => validA 6156 j3tReps[c]! &&
    eqA 6156 (powArr 6156 j3tReps[c]! 3) (idA 6156)) = true := by
  rw [allLt_iff]
  intro c hc
  rw [reps_get hc, valid_k (by omega), Bool.true_and,
    eqA_pow_id (rep_gp (by omega)) (gp_mem (by omega)) (hg (by omega)) 3]
  exact Orb.allN_iff.1 kCubes.2 c hc

theorem rec_lt : ∀ j < 13, j3tRec.getD j 0 < 2 := by decide

theorem trans_ok : transOK2 13 6156 j3tTrans j3tReps j3tLines j3tRec PairJ3.levels
    PairJ3.baseArr = true := by
  unfold transOK2
  rw [allLt_iff]
  intro j hj
  have hc := rec_lt j hj
  have hH := rep_gp (k := 20 + j) (by omega)
  have hX := rep_gp (k := 18 + j3tRec.getD j 0) (by omega)
  rw [trans_get hj, reps_get hc, lines_get hj, valid_k (by omega), sift_k (by omega),
    Bool.true_and, Bool.true_and]
  have hconj : Rep 6156 (conjA 6156 (unpack 6156 13 (F (20 + j))) (unpack 6156 13 (F (18 + j3tRec.getD j 0))))
      (gp (20 + j) * gp (18 + j3tRec.getD j 0) * (gp (20 + j))⁻¹) :=
    rep_conjA (valid_k (k := 20 + j) (by omega)) hX
  have hf : RepF 6156 (fun x => g (Nat.add 20 j) (g (Nat.add 18 (j3tRec.getD j 0)) (gi (Nat.add 20 j) x)))
      (gp (20 + j) * gp (18 + j3tRec.getD j 0) * (gp (20 + j))⁻¹) := by
    rw [mul_assoc]
    exact (hg (k := 20 + j) (by omega)).comp ((hg (k := 18 + j3tRec.getD j 0) (by omega)).comp
      (hgi (k := 20 + j) (by omega)))
  have _ := hH
  rw [eqA_eq hconj (rep_gp (by omega))
    (GJ.mul_mem (GJ.mul_mem (gp_mem (by omega)) (gp_mem (by omega))) (GJ.inv_mem (gp_mem (by omega))))
    (gp_mem (by omega)) hf (hg (by omega))]
  exact Orb.allN_iff.1 kTrans j hj

theorem rec_ok : allLt 13 (fun j => decide (j3tRec.getD j 0 < 2)) = true := by
  rw [allLt_iff]
  intro j hj
  exact decide_eq_true (rec_lt j hj)

theorem tc : TabChain 6156 13 5 4 PJ3.BP 97 64 PJ3T.NR PJ3T.NR 61 1024 7 1024 PJ3.S PJ3.SI PJ3.LR
    PJ3T.Ts PJ3T.LT PJ3T.PT PJ3T.QT j3StrongArrs PairJ3.baseArr PairJ3.bs :=
  ⟨PJ3Check.binds, PJ3Check.perm, PJ3.ho, by decide, PJ3Check.tabs, rfl⟩

theorem key_faith {a b : Array Nat} {A B : Equiv.Perm (Fin 6156)} (ha : Rep 6156 a A)
    (hb : Rep 6156 b B) (hA : A ∈ GJ) (hB : B ∈ GJ)
    (h : keyA 6156 j3tKeys a = keyA 6156 j3tKeys b) : A = B := by
  have hl := Nat.ofDigits_inj_of_len_eq (b := 6156) (by norm_num) (by simp)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [ha.apply (keys_lt p hp)]
      exact (A _).2)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [hb.apply (keys_lt p hp)]
      exact (B _).2) h
  refine eq_of_base hA hB fun c hc => ?_
  have hc' : c ∈ j3tKeys := hc
  have := List.map_inj_left.1 hl c hc'
  rwa [ha.apply (keys_lt c hc'), hb.apply (keys_lt c hc')] at this

theorem sk_lt {SK SKI : Nat → Nat} {N : Nat}
    (h : ∀ j < N, SKI j < N ∧ SK (SKI j) = j) : ∀ j < N, SK j < N := by
  have hinj : Set.InjOn SKI (Finset.range N : Set Nat) := fun a ha b hb e => by
    rw [← (h a (by simpa using ha)).2, ← (h b (by simpa using hb)).2, e]
  have himg : (Finset.range N).image SKI = Finset.range N := Finset.eq_of_subset_of_card_le
    (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_range.2 (h a (by simpa using ha)).1)
    (by rw [Finset.card_image_of_injOn hinj])
  intro j hj
  have : j ∈ (Finset.range N).image SKI := by rw [himg]; simpa using hj
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 this
  rw [(h a (by simpa using ha)).2]
  simpa using ha

theorem sort_parts {key SK SKI : Nat → Nat} {N : Nat} (h : allN N (sortAtK key SK SKI N) = true) :
    ∀ j < N, SKI j < N ∧ SK (SKI j) = j := fun j hj => by
  have h1 := Orb.allN_iff.1 h j hj
  unfold sortAtK at h1
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h1
  exact ⟨h1.1, Nat.eq_of_beq_eq_true h1.2.1⟩

theorem skA : ∀ j < 1080, TA.SK j < 1080 := sk_lt (sort_parts kSortA)

theorem skQ : ∀ j < 243, TQ.SK j < 243 := sk_lt (sort_parts kSortQ)

theorem base_get : ∀ l < 4, PairJ3.baseArr[l]! = bs.getD l 0 := by decide

theorem rels_ok {c : Nat} (hc : c < 2) {rels : List (Nat × Nat × Nat)}
    (h : rels.all (relAt (Nat.add 18 c)) = true) :
    relsOKP 3 6156 PairJ3.baseArr j3tReps[c]! rels = true := by
  unfold relsOKP
  rw [List.all_eq_true] at h ⊢
  intro r hr
  have h1 := h r hr
  unfold relAt at h1
  rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at h1
  obtain ⟨h2, h3, h4, h5⟩ := h1
  have hb : PairJ3.baseArr.size = 4 := rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hb]
  refine ⟨⟨⟨h2, h3⟩, h4⟩, ?_⟩
  have hx := rep_gp (k := 18 + c) (by omega)
  have hb1 : bs.getD r.1 0 < 6156 := by
    have : r.1 < 4 := h3
    interval_cases r.1 <;> decide
  rw [reps_get hc, base_get _ h3, base_get _ h4, (rep_powArr hx r.2.2).apply hb1,
    ← RepF.powF (hg (k := 18 + c) (by omega)) r.2.2 _ hb1]
  exact Nat.eq_of_beq_eq_true h5

theorem fr_ok {rels : List (Nat × Nat × Nat)} (h1 : (0, 1, 1) ∈ rels) (h2 : (1, 2, 1) ∈ rels) :
    ∀ i < 4, fr i = 0 ∨ ∃ l e, fr i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧ (l, i, e) ∈ rels := by
  intro i hi
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr ⟨0, 1, rfl, by norm_num, by norm_num, h1⟩
  · exact Or.inr ⟨1, 1, rfl, by norm_num, by norm_num, h2⟩
  · exact Or.inl rfl

theorem x_rep {c : Nat} (hc : c < 2) : Rep 6156 j3tReps[c]! (gp (18 + c)) := by
  rw [reps_get hc]
  exact rep_gp (by omega)

theorem tailA : ptailOK 6156 (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.baseArr
    j3tReps[0]! (powPA 3 6156 j3tReps[0]!) j3tRelsA j3tCACert.pts.toList 4 0 (idA 6156) = true := by
  refine ptailOK_of_ptK_ tc (x_rep (c := 0) (by norm_num)) (hg (k := 18) (by norm_num))
    (fun r hr => ?_) (fr_ok (by decide) (by decide)) bs_lt ?_ (by norm_num) kTailA
  · revert r
    decide
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ GJ := gen_le hA
    have hm := skA j hj
    unfold ka ta at e
    rw [← keyA_treeArr treeA hgA hgsA keys_lt hm, ← getA hm] at e
    have he := key_faith ha (repA hm) hR (memUA hm) e
    exact any_mem (by rw [sizeA]; exact hm) ((eqA_iff ha (repA hm)).2 he)

theorem tailB : ptailOK 6156 (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.baseArr
    j3tReps[1]! (powPA 3 6156 j3tReps[1]!) j3tRelsB j3tCBCert.pts.toList 4 0 (idA 6156) = true := by
  refine ptailOK_of_ptK_ tc (x_rep (c := 1) (by norm_num)) (hg (k := 19) (by norm_num))
    (fun r hr => ?_) (fr_ok (by decide) (by decide)) bs_lt ?_ (by norm_num) kTailB
  · revert r
    decide
  · intro a A ha hA ⟨j, hj, e⟩
    have hR : A ∈ GJ := gen_le hA
    have hm := skQ j hj
    unfold kq tq at e
    rw [← keyA_treeArr treeQ hgQ hgsQ keys_lt hm, ← getQ hm] at e
    have he := key_faith ha (repQ hm) hR (memUQ hm) e
    exact any_mem (by rw [sizeQ]; exact hm) ((eqA_iff ha (repQ hm)).2 he)

theorem cagens_get {k : Nat} (hk : k < 4) : j3tCAGens[k]! = unpack 6156 13 (F (33 + k)) := by
  rw [j3tCAGens, ofFn_get hk, arr_k (by omega)]

theorem cbgens_get {k : Nat} (hk : k < 5) : j3tCBGens[k]! = unpack 6156 13 (F k) := by
  rw [j3tCBGens, ofFn_get hk, arr_k (by omega), Nat.zero_add]

theorem dgens_get {k : Nat} (hk : k < 2) : j3tDGens[k]! = unpack 6156 13 (F (37 + k)) := by
  rw [j3tDGens, ofFn_get hk, arr_k (by omega)]

theorem comm_eq {a b : Nat} (ha : a < 40) (hb : b < 40) :
    commA 6156 (unpack 6156 13 (F a)) (unpack 6156 13 (F b)) =
      eqOnL bs (fun x => g a (g b x)) (fun x => g b (g a x)) :=
  eqA_eq (rep_compA (rep_gp ha) (rep_gp hb)) (rep_compA (rep_gp hb) (rep_gp ha))
    (GJ.mul_mem (gp_mem ha) (gp_mem hb)) (GJ.mul_mem (gp_mem hb) (gp_mem ha))
    ((hg ha).comp (hg hb)) ((hg hb).comp (hg ha))

theorem centA_ok : centOKP 3 6156 j3StrongArrs PairJ3.baseArr j3tReps[0]! j3tRelsA j3tCAGens
    j3tKeys j3tCACert 1080 = true := by
  have hs : j3tCAGens.size = 4 := by simp [j3tCAGens]
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff, hs]
  refine ⟨⟨⟨⟨⟨rels_ok (c := 0) (by norm_num) kRels.1, enumA⟩, sizeA⟩, fun k hk => ?_⟩,
    fun k hk => ?_⟩, tailA⟩
  · rw [cagens_get hk, reps_get (c := 0) (by norm_num), comm_eq (by omega) (by norm_num)]
    exact Orb.allN_iff.1 kComm.1 k hk
  · rw [cagens_get hk]
    exact sift_k (by omega)

theorem centB_ok : centOKP 3 6156 j3StrongArrs PairJ3.baseArr j3tReps[1]! j3tRelsB j3tCBGens
    j3tKeys j3tCBCert 243 = true := by
  have hs : j3tCBGens.size = 5 := by simp [j3tCBGens]
  simp only [centOKP, Bool.and_eq_true, beq_iff_eq, allLt_iff, hs]
  refine ⟨⟨⟨⟨⟨rels_ok (c := 1) (by norm_num) kRels.2, enumQ⟩, sizeQ⟩, fun k hk => ?_⟩,
    fun k hk => ?_⟩, tailB⟩
  · rw [cbgens_get hk, reps_get (c := 1) (by norm_num), comm_eq (by omega) (by norm_num)]
    exact Orb.allN_iff.1 kComm.2 k hk
  · rw [cbgens_get hk]
    exact sift_k (by omega)

theorem derived_ok : derivedLeOK 6156 j3tCAGens j3tDGens j3tKeys j3tDCert 360 = true := by
  have hs : j3tCAGens.size = 4 := by simp [j3tCAGens]
  have hs' : j3tDGens.size = 2 := by simp [j3tDGens]
  simp only [derivedLeOK, Bool.and_eq_true, beq_iff_eq, allLt_iff, hs, hs']
  refine ⟨⟨⟨enumD, sizeD⟩, fun k hk l hl => ?_⟩, fun k hk l hl => ?_⟩
  · have h := Orb.allN_iff.1 kDW.1 (2 * k + l) (by omega)
    have e1 : Nat.div (2 * k + l) 2 = k := by show (2 * k + l) / 2 = k; omega
    have e2 : Nat.mod (2 * k + l) 2 = l := by show (2 * k + l) % 2 = l; omega
    rw [e1, e2, bAnd_iff, Nat.blt_eq] at h
    obtain ⟨hw, he⟩ := h
    refine any_mem (k := DW.getD (2 * k + l) 0) (by rw [sizeD]; exact hw) ?_
    rw [cagens_get hk, dgens_get hl]
    have hc : Rep 6156 (conjA 6156 (unpack 6156 13 (F (33 + k))) (unpack 6156 13 (F (37 + l))))
        (gp (33 + k) * gp (37 + l) * (gp (33 + k))⁻¹) :=
      rep_conjA (valid_k (by omega)) (rep_gp (by omega))
    have hf : RepF 6156 (fun x => ga k (gd l (gi (Nat.add 33 k) x)))
        (gp (33 + k) * gp (37 + l) * (gp (33 + k))⁻¹) := by
      rw [mul_assoc]
      exact (hg (k := 33 + k) (by omega)).comp ((hg (k := 37 + l) (by omega)).comp
        (hgi (k := 33 + k) (by omega)))
    rw [eqA_eq hc (repD hw) (GJ.mul_mem (GJ.mul_mem (gp_mem (by omega)) (gp_mem (by omega)))
      (GJ.inv_mem (gp_mem (by omega)))) (memUD hw) hf (repFD hw)]
    exact eqOnL_symm he
  · have h := Orb.allN_iff.1 kDW.2 (4 * k + l) (by omega)
    have e1 : Nat.div (4 * k + l) 4 = k := by show (4 * k + l) / 4 = k; omega
    have e2 : Nat.mod (4 * k + l) 4 = l := by show (4 * k + l) % 4 = l; omega
    rw [e1, e2, bAnd_iff, Nat.blt_eq] at h
    obtain ⟨hw, he⟩ := h
    refine any_mem (k := DW.getD (Nat.add 8 (4 * k + l)) 0) (by rw [sizeD]; exact hw) ?_
    rw [cagens_get hk, cagens_get hl]
    have hc := rep_commutatorA (valid_k (k := 33 + k) (by omega)) (valid_k (k := 33 + l) (by omega))
    have hf : RepF 6156 (fun x => ga k (ga l (gi (Nat.add 33 k) (gi (Nat.add 33 l) x))))
        ⁅gp (33 + k), gp (33 + l)⁆ := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact (hg (k := 33 + k) (by omega)).comp ((hg (k := 33 + l) (by omega)).comp
        ((hgi (k := 33 + k) (by omega)).comp (hgi (k := 33 + l) (by omega))))
    have hmem : ⁅gp (33 + k), gp (33 + l)⁆ ∈ GJ := by
      rw [commutatorElement_def]
      exact GJ.mul_mem (GJ.mul_mem (GJ.mul_mem (gp_mem (by omega)) (gp_mem (by omega)))
        (GJ.inv_mem (gp_mem (by omega)))) (GJ.inv_mem (gp_mem (by omega)))
    rw [eqA_eq hc (repD hw) hmem (memUD hw) hf (repFD hw)]
    exact eqOnL_symm he

noncomputable def wpD : List (Fin 2 × Bool) → Equiv.Perm (Fin 6156)
  | [] => 1
  | a :: w => (if a.2 then gp (37 + a.1.val) else (gp (37 + a.1.val))⁻¹) * wpD w

theorem evalWA_cons (a : Fin 2 × Bool) (w : List (Fin 2 × Bool)) :
    evalWA 6156 j3tDGens (a :: w) = compA 6156 (if a.2 then j3tDGens[a.1.val]! else
      invCand 6156 j3tDGens[a.1.val]!) (evalWA 6156 j3tDGens w) := rfl

theorem wvD_cons (a : Fin 2 × Bool) (w : List (Fin 2 × Bool)) (x : Nat) :
    wvD (a :: w) x = Bool.rec (motive := fun _ => Nat) (gi (Nat.add 37 a.1.val) (wvD w x))
      (g (Nat.add 37 a.1.val) (wvD w x)) a.2 := rfl

theorem wpD_cons (a : Fin 2 × Bool) (w : List (Fin 2 × Bool)) :
    wpD (a :: w) = (if a.2 then gp (37 + a.1.val) else (gp (37 + a.1.val))⁻¹) * wpD w := by
  rw [wpD]

theorem letter_facts (a : Fin 2 × Bool) :
    Rep 6156 (if a.2 then j3tDGens[a.1.val]! else invCand 6156 j3tDGens[a.1.val]!)
        (if a.2 then gp (37 + a.1.val) else (gp (37 + a.1.val))⁻¹) ∧
      RepF 6156 (fun x => Bool.rec (motive := fun _ => Nat) (gi (Nat.add 37 a.1.val) x)
        (g (Nat.add 37 a.1.val) x) a.2) (if a.2 then gp (37 + a.1.val) else (gp (37 + a.1.val))⁻¹) ∧
      (if a.2 then gp (37 + a.1.val) else (gp (37 + a.1.val))⁻¹) ∈ GJ := by
  have ha : a.1.val < 2 := a.1.2
  have hk : 37 + a.1.val < 40 := by omega
  rw [dgens_get ha]
  cases a.2
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, (inv_k hk).1]
    exact ⟨rep_gpi hk, hgi hk, GJ.inv_mem (gp_mem hk)⟩
  · rw [if_pos rfl, if_pos rfl]
    exact ⟨rep_gp hk, hg hk, gp_mem hk⟩

theorem wordD_facts (w : List (Fin 2 × Bool)) :
    Rep 6156 (evalWA 6156 j3tDGens w) (wpD w) ∧ RepF 6156 (wvD w) (wpD w) ∧ wpD w ∈ GJ := by
  induction w with
  | nil => exact ⟨rep_idA, RepF.one, GJ.one_mem⟩
  | cons a w ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨l1, l2, l3⟩ := letter_facts a
    rw [evalWA_cons, wpD_cons]
    refine ⟨rep_compA l1 h1, fun x hx => ?_, GJ.mul_mem l3 h3⟩
    rw [wvD_cons]
    exact (l2.comp h2) x hx

theorem wordsOne_ok : wordsOneOK 6156 j3tDGens j3tA6Rels = true := by
  have hs' : j3tDGens.size = 2 := by simp [j3tDGens]
  unfold wordsOneOK
  rw [Bool.and_eq_true, allLt_iff, hs', List.all_eq_true]
  refine ⟨fun l hl => ?_, fun w hw => ?_⟩
  · rw [dgens_get hl]
    exact valid_k (by omega)
  · obtain ⟨h1, h2, h3⟩ := wordD_facts w
    rw [eqA_eq h1 rep_idA h3 GJ.one_mem h2 RepF.one]
    exact List.all_eq_true.1 kRelD w hw

theorem siftD_ok : allLt 2 (fun l => siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tDGens[l]!) =
    true := by
  rw [allLt_iff]
  intro l hl
  rw [dgens_get hl]
  exact sift_k (by omega)

theorem siftG_ok : siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tG = true := by
  rw [g_get]
  exact sift_k (by norm_num)

theorem det_ok : detOK 6156 j3tDGens j3tG j3tWu j3tWv 1 = true := by
  obtain ⟨u1, u2, u3⟩ := wordD_facts j3tWu
  obtain ⟨v1, v2, v3⟩ := wordD_facts j3tWv
  have hG := rep_gp (k := 39) (by norm_num)
  have hGm := gp_mem (k := 39) (by norm_num)
  have h := kDet
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨d1, d2, d3⟩ := h
  unfold detOK
  simp only [Bool.and_eq_true]
  rw [g_get]
  refine ⟨⟨⟨valid_k (by norm_num), ?_⟩, ?_⟩, ?_⟩
  · have hc : Rep 6156 (conjA 6156 (unpack 6156 13 (F 39)) (evalWA 6156 j3tDGens j3tWu))
        (gp 39 * wpD j3tWu * (gp 39)⁻¹) := rep_conjA (valid_k (by norm_num)) u1
    have hf : RepF 6156 (fun x => g 39 (uF (gi 39 x))) (gp 39 * wpD j3tWu * (gp 39)⁻¹) := by
      rw [mul_assoc]
      exact (hg (k := 39) (by norm_num)).comp (u2.comp (hgi (k := 39) (by norm_num)))
    rw [eqA_eq hc v1 (GJ.mul_mem (GJ.mul_mem hGm u3) (GJ.inv_mem hGm)) v3 hf v2]
    exact d1
  · have hc : Rep 6156 (conjA 6156 (unpack 6156 13 (F 39)) (evalWA 6156 j3tDGens j3tWv))
        (gp 39 * wpD j3tWv * (gp 39)⁻¹) := rep_conjA (valid_k (by norm_num)) v1
    have hf : RepF 6156 (fun x => g 39 (vF (gi 39 x))) (gp 39 * wpD j3tWv * (gp 39)⁻¹) := by
      rw [mul_assoc]
      exact (hg (k := 39) (by norm_num)).comp (v2.comp (hgi (k := 39) (by norm_num)))
    rw [eqA_eq hc (rep_compA u1 (rep_powArr v1 1))
      (GJ.mul_mem (GJ.mul_mem hGm v3) (GJ.inv_mem hGm)) (GJ.mul_mem u3 (GJ.pow_mem v3 1)) hf
      (u2.comp (RepF.powF v2 1))]
    exact d2
  · rw [eqA_eq (rep_compA u1 v1) (rep_compA v1 u1) (GJ.mul_mem u3 v3) (GJ.mul_mem v3 u3)
      (u2.comp v2) (v2.comp u2)]
    exact d3

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
open Certificates in
theorem facts :
    (linesOK3 3 243 13 6156 j3tCBGens j3tKeys j3tCBCert j3tLines = true ∧
      allLt 2 (fun c => validA 6156 j3tReps[c]! &&
        eqA 6156 (powArr 6156 j3tReps[c]! 3) (idA 6156)) = true ∧
      transOK2 13 6156 j3tTrans j3tReps j3tLines j3tRec PairJ3.levels PairJ3.baseArr = true ∧
      allLt 13 (fun j => decide (j3tRec.getD j 0 < 2)) = true) ∧
    (centOKP 3 6156 j3StrongArrs PairJ3.baseArr j3tReps[0]! j3tRelsA j3tCAGens j3tKeys
        j3tCACert 1080 = true ∧
      centOKP 3 6156 j3StrongArrs PairJ3.baseArr j3tReps[1]! j3tRelsB j3tCBGens j3tKeys
        j3tCBCert 243 = true) ∧
    (derivedLeOK 6156 j3tCAGens j3tDGens j3tKeys j3tDCert 360 = true ∧
      wordsOneOK 6156 j3tDGens j3tA6Rels = true ∧
      allLt 2 (fun l => siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tDGens[l]!) = true ∧
      siftA 6156 PairJ3.levels PairJ3.baseArr 0 j3tG = true ∧
      detOK 6156 j3tDGens j3tG j3tWu j3tWv 1 = true) :=
  ⟨⟨lines_ok, reps_ok, trans_ok, rec_ok⟩, ⟨centA_ok, centB_ok⟩,
    ⟨derived_ok, wordsOne_ok, siftD_ok, siftG_ok, det_ok⟩⟩

end CertificateChecks.KernelK426J3

end
