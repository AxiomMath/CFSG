module

public import Certificates.Kernel.RuFive.Base
public import CFSG.RankThree.PartOne.KS.PKitLines
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.J2H
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.Certificates CFSG.Certificates.Native


theorem eq_of_R {f f' : Nat → Nat} {x y : Equiv.Perm (Fin 4060)} (hf : RepF 4060 f x)
    (hf' : RepF 4060 f' y) (hx : x ∈ ruP) (hy : y ∈ ruP) (h : eqOnL bs f f' = true) : x = y :=
  eq_of_eqOnL faith0.1 hf hf' hx hy h

theorem eqA_R {t u : Array Nat} {x y : Equiv.Perm (Fin 4060)} {f f' : Nat → Nat}
    (ht : Rep 4060 t x) (hu : Rep 4060 u y) (hf : RepF 4060 f x) (hf' : RepF 4060 f' y)
    (hx : x ∈ ruP) (hy : y ∈ ruP) (h : eqOnL bs f f' = true) : eqA 4060 t u = true :=
  (eqA_iff ht hu).2 (eq_of_R hf hf' hx hy h)

theorem neA_R {t u : Array Nat} {x y : Equiv.Perm (Fin 4060)} {f f' : Nat → Nat}
    (ht : Rep 4060 t x) (hu : Rep 4060 u y) (hf : RepF 4060 f x) (hf' : RepF 4060 f' y)
    (h : eqOnL bs f f' = false) : eqA 4060 t u = false := by
  rw [Bool.eq_false_iff]
  intro he
  have e := (eqA_iff ht hu).1 he
  rw [e] at hf
  rw [eqOnL_of_eq bs_lt hf hf'] at h
  exact absurd h (by decide)

theorem commA_R {t u : Array Nat} {x y : Equiv.Perm (Fin 4060)} {f f' : Nat → Nat}
    (ht : Rep 4060 t x) (hu : Rep 4060 u y) (hf : RepF 4060 f x) (hf' : RepF 4060 f' y)
    (hx : x ∈ ruP) (hy : y ∈ ruP)
    (h : eqOnL bs (fun z => f (f' z)) (fun z => f' (f z)) = true) : commA 4060 t u = true :=
  eqA_R (rep_compA ht hu) (rep_compA hu ht) (hf.comp hf') (hf'.comp hf) (ruP.mul_mem hx hy)
    (ruP.mul_mem hy hx) h

theorem any_mem {c : ArrCert} {t : Array Nat} {k : Nat}
    (hk : k < c.pts.size) (h : eqA 4060 t c.pts[k]! = true) :
    c.pts.toList.any (eqA 4060 t) = true := by
  rw [List.any_eq_true]
  refine ⟨c.pts[k]!, ?_, h⟩
  rw [getElem!_pos c.pts k hk]
  exact Array.getElem_mem_toList _

theorem eqOnL_symm {l : List Nat} {f g : Nat → Nat} (h : eqOnL l f g = true) :
    eqOnL l g f = true :=
  (eqOnL_iff _ _ _).2 fun b hb => ((eqOnL_iff _ _ _).1 h b hb).symm

theorem key_faith {a b : Array Nat} {A B : Equiv.Perm (Fin 4060)} (ha : Rep 4060 a A)
    (hb : Rep 4060 b B) (hA : A ∈ ruP) (hB : B ∈ ruP)
    (h : keyA 4060 ruFiveKeys a = keyA 4060 ruFiveKeys b) : A = B := by
  have hl := Nat.ofDigits_inj_of_len_eq (b := 4060) (by norm_num) (by simp)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [ha.apply (keys_lt p hp)]
      exact (A _).2)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [hb.apply (keys_lt p hp)]
      exact (B _).2) h
  have hpt : ∀ p (hp : p ∈ ruFiveKeys), (A ⟨p, keys_lt p hp⟩ : Nat) = B ⟨p, keys_lt p hp⟩ := by
    intro p hp
    have := List.map_inj_left.1 hl p hp
    rwa [ha.apply (keys_lt p hp), hb.apply (keys_lt p hp)] at this
  exact hF A hA B hB (iff_of_true hA hB) hpt

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

theorem rep_line (j : Nat) (hj : j < 31) : Rep 4060 ruFiveLines[j]! (gp (2 + j)) := by
  rw [ruFiveLines, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    show j + 2 = 2 + j by omega, arr_eq (2 + j) (by omega)]
  exact rep_gp _ (by omega)

theorem repF_ln (j : Nat) (hj : j < 31) : RepF 4060 (ln j) (gp (2 + j)) :=
  repF_pa (2 + j) (by omega)

theorem ln_mem (j : Nat) (hj : j < 31) : gp (2 + j) ∈ ruP := gp_mem _ (by omega)

theorem trans_eq (j : Nat) (hj : j < 31) :
    ruFiveTransporters[j]! = unpack 4060 12 (F (33 + j)) := by
  rw [ruFiveTransporters, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    show j + 33 = 33 + j by omega]
  exact arr_eq (33 + j) (by omega)

theorem qgens_eq (k : Nat) (hk : k < 2) : ruFiveQGens[k]! = unpack 4060 12 (F k) := by
  rw [ruFiveQGens]
  interval_cases k
  · exact arr_eq 0 (by norm_num)
  · exact arr_eq 1 (by norm_num)

theorem qgs : ∀ k < 2, Rep 4060 ruFiveQGens[k]! (gp k) := fun k hk => by
  rw [qgens_eq k hk]
  exact rep_gp k (by omega)

theorem qg : ∀ k < 2, RepF 4060 (gQ k) (gp k) := fun k hk => repF_pa k (by omega)

theorem qg_mem : ∀ k < 2, gp k ∈ ruP := fun k hk => gp_mem k (by omega)

theorem qtree : TreeOK 2 125 Q.P Q.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kQTree i hi
  rwa [beq_zero_false h0] at h

theorem tq_mem {i : Nat} (hi : i < 125) : treePerm gp Q.P Q.L i ∈ ruP :=
  (trQ_spec qtree hmul qg_mem (fun k hk => iff_of_true (qg_mem k hk) rfl) (fun _ _ => by decide)
    125 i hi.le hi).1

theorem qedges : ∀ i < 125, ∀ k < 2, QE i k < 125 ∧
    treeArr 4060 ruFiveQGens Q.P Q.L (QE i k) =
      compA 4060 ruFiveQGens[k]! (treeArr 4060 ruFiveQGens Q.P Q.L i) :=
  edges_of_edgeAtK qtree qg qgs hmul qg_mem (fun k hk => iff_of_true (qg_mem k hk) rfl)
    (fun _ _ => by decide) bs_lt hF fun i hi => Orb.allN_iff.1 kQEdge i hi

theorem qkeys_inj : ∀ a < 125, ∀ b < 125,
    keyA 4060 ruFiveKeys (treeArr 4060 ruFiveQGens Q.P Q.L a) =
      keyA 4060 ruFiveKeys (treeArr 4060 ruFiveQGens Q.P Q.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := qkey) fun j hj => Orb.allN_iff.1 kQSort j hj
  intro a ha b hb e
  rw [keyA_treeArr qtree qg qgs keys_lt ha, keyA_treeArr qtree qg qgs keys_lt hb] at e
  exact hk a ha b hb e

theorem q_pts : ruFiveQCert.pts =
    Array.ofFn (n := 125) fun i => treeArr 4060 ruFiveQGens Q.P Q.L i.val :=
  enumBfs_tree qtree qgs (by rfl) (by norm_num) (by norm_num) qkeys_inj qedges kQReplay

theorem q_enum : enumOK 4060 ruFiveQGens ruFiveKeys ruFiveQCert = true :=
  enumOK_tree qtree qgs (by rfl) (by norm_num) (by norm_num) qkeys_inj qedges

theorem q_get {k : Nat} (hk : k < 125) :
    ruFiveQCert.pts[k]! = treeArr 4060 ruFiveQGens Q.P Q.L k := by
  rw [q_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem q_rep {k : Nat} (hk : k < 125) : Rep 4060 ruFiveQCert.pts[k]! (treePerm gp Q.P Q.L k) := by
  rw [q_get hk]
  exact rep_treeArr qtree qgs k hk

theorem q_repF {k : Nat} (hk : k < 125) : RepF 4060 (qv k) (treePerm gp Q.P Q.L k) :=
  repF_trV qtree qg 125 k hk.le hk

theorem lines : linesOK 4060 ruFiveQGens ruFiveKeys ruFiveQCert ruFiveLines = true := by
  change linesOKG 5 125 31 4060 ruFiveQGens ruFiveKeys ruFiveQCert ruFiveLines = true
  have hN : ruFiveQCert.pts.size = 125 := by rw [q_pts, Array.size_ofFn]
  simp only [linesOKG, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨q_enum, hN⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩
  · exact eqA_R (rep_powArr (q_rep hk) 5) rep_idA (RepF.powF (q_repF hk) 5) RepF.one
      (ruP.pow_mem (tq_mem hk) 5) ruP.one_mem (Orb.allN_iff.1 kQPow k hk)
  · have hc := Orb.allN_iff.1 kCover k hk
    unfold coverAt at hc
    rw [CFSG.KS.SporSch.strictB_val] at hc
    rw [Bool.or_eq_true, List.any_eq_true]
    by_cases hw : QW.getD k 0 = 0
    · rw [hw] at hc
      exact Or.inl (eqA_R (q_rep hk) rep_idA (q_repF hk) RepF.one (tq_mem hk) ruP.one_mem hc)
    · rw [show Nat.beq (QW.getD k 0) 0 = false from Bool.eq_false_iff.2 fun h =>
        hw (Nat.eq_of_beq_eq_true h)] at hc
      simp only [bAnd_iff, Nat.blt_eq] at hc
      obtain ⟨h1, h2, h3, h4⟩ := hc
      refine Or.inr ⟨QW.getD k 0 / 8, List.mem_range.2 h1, ?_⟩
      rw [List.any_eq_true]
      refine ⟨QW.getD k 0 % 8, List.mem_range.2 h3, ?_⟩
      exact eqA_R (q_rep hk) (rep_powArr (rep_line _ h1) _) (q_repF hk)
        (RepF.powF (repF_ln _ h1) _) (tq_mem hk) (ruP.pow_mem (ln_mem _ h1) _) h4
  · intro j' hj'
    have hd := Orb.allN_iff.1 (Orb.allN_iff.1 kDist j hj) j' hj'
    unfold distAt at hd
    rw [Bool.or_eq_true, allLt_iff]
    by_cases e : j = j'
    · exact Or.inl (by simp [e])
    · right
      intro m hm
      rw [show Nat.beq j j' = false from Bool.eq_false_iff.2 fun h => e (Nat.eq_of_beq_eq_true h)]
        at hd
      have h1 := Orb.allN_iff.1 hd m hm
      rw [Bool.not_eq_true'] at h1
      rw [Bool.not_eq_true']
      exact neA_R (rep_line j hj) (rep_powArr (rep_line j' hj') m) (repF_ln j hj)
        (RepF.powF (repF_ln j' hj') m) (by simpa using h1)
  · have hl := Orb.allN_iff.1 kLine j hj
    unfold lineAt at hl
    simp only [bAnd_iff, Nat.blt_eq, Bool.not_eq_true'] at hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    refine ⟨⟨⟨CFSG.RankThree.Native.F2.validA_of_rep (rep_line j hj), ?_⟩, ?_⟩, ?_⟩
    · exact eqA_R (rep_powArr (rep_line j hj) 5) rep_idA (RepF.powF (repF_ln j hj) 5) RepF.one
        (ruP.pow_mem (ln_mem j hj) 5) ruP.one_mem h1
    · rw [Bool.not_eq_true']
      exact neA_R (rep_line j hj) rep_idA (repF_ln j hj) RepF.one h2
    · rw [List.any_eq_true]
      refine ⟨ruFiveQCert.pts[LQ.getD j 0]!, ?_, ?_⟩
      · rw [getElem!_pos _ _ (by rw [hN]; exact h3)]
        exact Array.getElem_mem_toList _
      · exact eqA_R (rep_line j hj) (q_rep h3) (repF_ln j hj) (q_repF h3) (ln_mem j hj)
          (tq_mem h3) (eqOnL_symm h4)

theorem qsift : allLt ruFiveQGens.size
    (fun l => siftA 4060 ruPLevels ruCase0BaseArr 0 ruFiveQGens[l]!) = true := by
  rw [allLt_iff]
  intro l hl
  have hl2 : l < 2 := hl
  exact (sift0_iff (qgs l hl2)).2 (qg_mem l hl2)

theorem rec_lt : ∀ j < 31, ruFiveRec.getD j 0 < 2 := by decide

theorem trans : transOK 4060 ruFiveTransporters ruFiveLines ruFiveRec ruPLevels ruCase0BaseArr =
    true := by
  change transOKG 31 4060 ruFiveTransporters ruFiveLines ruFiveRec ruPLevels ruCase0BaseArr = true
  unfold transOKG
  rw [allLt_iff]
  intro j hj
  have hH : Rep 4060 ruFiveTransporters[j]! (gp (33 + j)) := by
    rw [trans_eq j hj]
    exact rep_gp _ (by omega)
  have hr := rec_lt j hj
  have hr31 : ruFiveRec.getD j 0 % 31 = ruFiveRec.getD j 0 := Nat.mod_eq_of_lt (by omega)
  have hL := rep_line (ruFiveRec.getD j 0) (by omega)
  have hc := rep_conjA (CFSG.RankThree.Native.F2.validA_of_rep hH) hL
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hH] at hc
  have hHm := gp_mem (33 + j) (by omega)
  simp only [Bool.and_eq_true]
  refine ⟨⟨CFSG.RankThree.Native.F2.validA_of_rep hH, (sift0_iff hH).2 hHm⟩, ?_⟩
  rw [hr31]
  have hcf : RepF 4060 (fun y => pa (Nat.add 33 j) (ln (ruFiveRec.getD j 0) (pi (Nat.add 33 j) y)))
      (gp (33 + j) * gp (2 + ruFiveRec.getD j 0) * (gp (33 + j))⁻¹) := by
    have := (repF_pa (33 + j) (by omega)).comp ((repF_ln (ruFiveRec.getD j 0) (by omega)).comp
      (repF_pi (33 + j) (by omega)))
    rw [mul_assoc]
    exact this
  exact eqA_R hc (rep_line j hj) hcf (repF_ln j hj)
    (ruP.mul_mem (ruP.mul_mem hHm (ln_mem _ (by omega))) (ruP.inv_mem hHm)) (ln_mem j hj)
    (Orb.allN_iff.1 kTrans j hj)

theorem qfacts : linesOK 4060 ruFiveQGens ruFiveKeys ruFiveQCert ruFiveLines = true ∧
    allLt ruFiveQGens.size (fun l => siftA 4060 ruPLevels ruCase0BaseArr 0 ruFiveQGens[l]!) =
      true ∧
    transOK 4060 ruFiveTransporters ruFiveLines ruFiveRec ruPLevels ruCase0BaseArr = true ∧
    ruFiveRec.getD 0 0 = 0 ∧ ruFiveRec.getD 1 0 = 1 ∧
    allLt 31 (fun j => ruFiveRec.getD j 0 == 0 || ruFiveRec.getD j 0 == 1) = true :=
  ⟨lines, qsift, trans, by decide, by decide, by rw [allLt_iff]; decide⟩

end CertificateChecks.KernelRuFive

end
