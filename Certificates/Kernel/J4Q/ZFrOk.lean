module

public import Certificates.Kernel.J4Q.ZFrM
public import CFSG.Certificates.Kernel.J4Q.ZFrTab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

theorem two_pow_lt {j : Nat} (hj : j < 11) : 2 ^ j < 2048 := by
  have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hj
  simpa using this

theorem getD_lt_of_lenOK {T : List Nat} (hT : lenOK T = true) {j : Nat} (hj : j < 11) :
    T.getD j 0 < 2048 := by
  obtain ⟨hl, hx⟩ := lenOK_iff hT
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simpa using hx _ (List.getElem_mem (by omega))

theorem tabOK_of (hE : ∀ t < 32, etaCK t = true) {M : Array V2} {m : Nat} (hM : WfA M ∧ encR M = m)
    {T : List Nat} (h : tabOKK m T = true) : zTabOK M M T = true := by
  unfold tabOKK at h
  unfold zTabOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h ⊢
  refine ⟨h.1, fun j hj => ?_⟩
  rw [eqRows_of (mul_enc hK (mul_enc hK hM (ef_enc hE (two_pow_lt hj))) hM)
    (ef_enc hE (getD_lt_of_lenOK h.1 hj))]
  exact h.2 j hj

theorem prod_map_enc (hE : ∀ t < 32, etaCK t = true) {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t)
    (gw : List Int) : ∀ l : List (Fin 4),
    List.Forall₂ (fun X x => WfA X ∧ encR X = x) (l.map (zMs T gw)) (l.map fun j => msK t gw j)
  | [] => List.Forall₂.nil
  | j :: l => List.Forall₂.cons (ms_enc hE hT gw j) (prod_map_enc hE hT gw l)

theorem light_of (hE : ∀ t < 32, etaCK t = true) {T₀ : Array V2} {t0 : Nat} (hT : WfA T₀ ∧ encR T₀ = t0)
    {gw : List Int} {Ts : List (List Nat)} (h : zfLightK t0 gw Ts = true) : chkZLightT T₀ gw Ts = true := by
  have hms := ms_enc hE hT gw
  have hY : WfA (zYR gw) ∧ encR (zYR gw) = conjByK gw (getN one XG 0) := conjBy_enc zfXi_enc gw
  have hYi : WfA (zYiR gw) ∧ encR (zYiR gw) = conjByK gw (getN one XG 8) := conjBy_enc xiI_enc' gw
  unfold zfLightK at h
  unfold chkZLightT
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h ⊢
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨⟨⟨⟨⟨h1, ?_⟩, fun i => ⟨⟨wf_bool (hms i).1, ?_⟩, ?_⟩⟩, fun i j => ?_⟩, wf_bool hY.1⟩, fun i => ?_⟩
  · rw [eqRows_of (conjBy_enc hT gw) (ef_enc hE (by decide))]
    exact h2
  · rw [eqRows_of (mul_enc hK (hms i) (hms i)) (id_enc hK)]
    exact (h3 i).1
  · exact tabOK_of hE (hms i) (h3 i).2
  · rw [eqRows_of (mul_enc hK (hms i) (hms j)) (mul_enc hK (hms j) (hms i))]
    exact h4 i j
  · rw [eqRows_of (mul_enc hK (mul_enc hK hY (hms i)) hYi) (zfProd_enc (prod_map_enc hE hT gw _))]
    exact h5 i

theorem masks_mem_lt {TsB d : List Nat} {c' : Nat} (h : c' ∈ zfMasksB TsB d) : c' < 2048 := by
  unfold zfMasksB at h
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem surv_of (hE : ∀ t < 32, etaCK t = true) {T₀ : Array V2} {t0 : Nat} (hT : WfA T₀ ∧ encR T₀ = t0)
    {gw : List Int} {Ts : List (List Nat)} {TsB : List Nat} (hTs : Ts = TsB.map unpackP)
    (hTl : TsB.length = 4) {C : List (List (List Nat))} {surv sq D : List (List Nat)} {E : List Nat}
    {u : Nat} (h : zfSurvK t0 gw TsB C surv sq D E u = true) :
    zfSurvOK (zMs T₀ gw) Ts C surv sq D E u = true := by
  have hms := ms_enc hE hT gw
  have hmk : zfMasks Ts (D.getD u []) = zfMasksB TsB (D.getD u []) := by
    rw [hTs]
    exact zfMasks_eqB TsB _ hTl
  unfold zfSurvK at h
  unfold zfSurvOK
  rw [hmk]
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨h1, h0⟩, he⟩, h2⟩, h3⟩, h4⟩ := h
  have hd : ∀ i : Fin 4, (D.getD u []).getD i 0 < 2048 := by
    intro i
    by_cases hi : (i : Nat) < (D.getD u []).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      simpa using h0 _ (List.getElem_mem hi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      norm_num
  refine ⟨⟨⟨⟨⟨h1, h0⟩, he⟩, h2⟩, fun i => ?_⟩, ?_⟩
  · rw [eqRows_of (mul_enc hK (mul_enc hK (mul_enc hK (hms i) (seqR_enc _)) (hms i)) (seqRi_enc _))
      (ef_enc hE (hd i))]
    exact h3 i
  · rcases h4 with h4 | ⟨h5, h6⟩
    · exact Or.inl h4
    · right
      refine ⟨?_, h6⟩
      rw [eqRows_of (mul_enc hK (seqR_enc _) (seqR_enc _)) (ef_enc hE he)]
      exact h5

theorem zfI_eqB {Ts : List (List Nat)} {TsB : List Nat} (hTs : Ts = TsB.map unpackP)
    (hTl : TsB.length = 4) (surv D : List (List Nat)) : zfI Ts surv D = zfIB TsB surv D := by
  unfold zfI zfIB
  refine zfFlatMap_congr fun u _ => ?_
  rw [hTs, zfMasks_eqB TsB _ hTl]

theorem count_of (hE : ∀ t < 32, etaCK t = true) {gw : List Int} {Ts : List (List Nat)}
    {TsB : List Nat} (hTs : Ts = TsB.map unpackP) (hTl : TsB.length = 4) {surv sq D : List (List Nat)}
    {k : Nat} (h : zfCountK gw TsB surv sq D k = true) :
    ((zfI Ts surv D).filter fun q =>
      eqRows (mulRows (zfRowsOf sq q) (zYR gw)) (mulRows (zYR gw) (zfRowsOf sq q))).length ≤ k ∧
      16 * k < (zfI Ts surv D).length := by
  have hY := conjBy_enc zfXi_enc gw
  unfold zfCountK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [zfI_eqB hTs hTl]
  refine ⟨?_, h.2⟩
  have e : ((zfIB TsB surv D).filter fun q =>
      eqRows (mulRows (zfRowsOf sq q) (zYR gw)) (mulRows (zYR gw) (zfRowsOf sq q))) =
      (zfIB TsB surv D).filter fun q =>
        Nat.beq (mulJ c rm (mulJ c rm (CFSG.KD.ETA.EF q.2) (seqRK (sq.getD q.1 []))) (conjByK gw (getN one XG 0)))
          (mulJ c rm (conjByK gw (getN one XG 0)) (mulJ c rm (CFSG.KD.ETA.EF q.2) (seqRK (sq.getD q.1 [])))) := by
    refine zfFilter_congr fun q hq => ?_
    unfold zfIB at hq
    obtain ⟨u, -, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hq
    have hR := mul_enc hK (ef_enc hE (masks_mem_lt hc')) (seqR_enc (sq.getD u []))
    unfold zfRowsOf
    exact eqRows_of (mul_enc hK hR hY) (mul_enc hK hY hR)
  rw [e]
  exact h.1

theorem all_range32_of {f : Nat → Bool} (h0 : ((List.range 8).all fun i => f (0 + i)) = true)
    (h1 : ((List.range 8).all fun i => f (8 + i)) = true) (h2 : ((List.range 8).all fun i => f (16 + i)) = true)
    (h3 : ((List.range 8).all fun i => f (24 + i)) = true) : (List.range 32).all f = true := by
  refine List.all_eq_true.2 fun u hu => ?_
  have hu' := List.mem_range.1 hu
  have key : ∀ (lo : Nat) (h : ((List.range 8).all fun i => f (lo + i)) = true), lo ≤ u → u < lo + 8 →
      f u = true := by
    intro lo h hl hr
    have := List.all_eq_true.1 h (u - lo) (List.mem_range.2 (by omega))
    rwa [Nat.add_sub_cancel' hl] at this
  by_cases a : u < 8
  · exact key 0 h0 (by omega) (by omega)
  by_cases b : u < 16
  · exact key 8 h1 (by omega) (by omega)
  by_cases d : u < 24
  · exact key 16 h2 (by omega) (by omega)
  · exact key 24 h3 (by omega) (by omega)

theorem chkZFr_of (hE : ∀ t < 32, etaCK t = true) {e : Nat} (he : e < 2048) {gw : List Int} {k : Nat}
    {Ts : List (List Nat)} {TsB VsB : List Nat} (hTs : Ts = TsB.map unpackP) (hTl : TsB.length = 4)
    (hV : zfVs Ts = VsB.map unpackP) {base : List Nat} {C : List (List (List Nat))}
    {surv sq D : List (List Nat)} {E : List Nat}
    (h1 : zfLightK (mulJ c rm (CFSG.KD.ETA.EF e) (gwK zB336Word)) gw Ts = true)
    (h2 : zfChainOK C base = true) (h3 : (C.map List.length).prod = 887040)
    (h4 : (zfBtGoB TsB VsB C base [] ZIDB [] == surv) = true)
    (h5 : (sq.length == surv.length && D.length == surv.length &&
      decide ((List.range surv.length).map fun u => zfSeqT (sq.getD u [])).Nodup) = true)
    (h6 : (List.range surv.length).all
      (zfSurvK (mulJ c rm (CFSG.KD.ETA.EF e) (gwK zB336Word)) gw TsB C surv sq D E) = true)
    (h7 : zfCountK gw TsB surv sq D k = true) :
    chkZFr k (zB336T0 e) gw Ts base C surv sq D E = true := by
  have hT0 : WfA (zB336T0 e) ∧ encR (zB336T0 e) = mulJ c rm (CFSG.KD.ETA.EF e) (gwK zB336Word) :=
    mul_enc hK (ef_enc hE he) (gw_enc _)
  have hbt : zfBt Ts C base = surv := by
    rw [zfBt_eqB hTs hV base (zfChain_seq h2)]
    exact beq_iff_eq.1 h4
  have hc := count_of hE hTs hTl h7
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h5
  unfold chkZFr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨light_of hE hT0 h1, h2⟩, h3⟩, hbt⟩, h5.1.1⟩, h5.1.2⟩, h5.2⟩, ?_⟩, hc.1⟩, hc.2⟩
  refine List.all_eq_true.2 fun u hu => ?_
  exact surv_of hE hT0 hTs hTl (List.all_eq_true.1 h6 u hu)

theorem chkZFr_of_parts (hE : ∀ t < 32, etaCK t = true) {e : Nat} (he : e < 2048) {gw : List Int}
    {Ts : List (List Nat)} {TsB VsB base : List Nat} {C : List (List (List Nat))}
    {surv sq D : List (List Nat)} {E : List Nat}
    (h : ∀ p < 8, zfPart e gw Ts TsB VsB base C surv sq D E p = true) :
    chkZFr 4 (zB336T0 e) gw Ts base C surv sq D E = true := by
  have h1 : zfStatK Ts TsB VsB base C surv sq D = true := h 1 (by decide)
  unfold zfStatK at h1
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hTs, hTl⟩, hV⟩, hC⟩, hP⟩, hL⟩, hsq⟩, hD⟩, hN⟩ := h1
  have f3 : ((List.range 8).all fun i => zfSurvK (t0K e) gw TsB C surv sq D E (0 + i)) = true :=
    h 3 (by decide)
  have f4 : ((List.range 8).all fun i => zfSurvK (t0K e) gw TsB C surv sq D E (8 + i)) = true :=
    h 4 (by decide)
  have f5 : ((List.range 8).all fun i => zfSurvK (t0K e) gw TsB C surv sq D E (16 + i)) = true :=
    h 5 (by decide)
  have f6 : ((List.range 8).all fun i => zfSurvK (t0K e) gw TsB C surv sq D E (24 + i)) = true :=
    h 6 (by decide)
  have h6 : (List.range surv.length).all (zfSurvK (t0K e) gw TsB C surv sq D E) = true := by
    rw [hL]
    exact all_range32_of f3 f4 f5 f6
  refine chkZFr_of hE he hTs hTl hV (h 0 (by decide)) hC hP (h 2 (by decide)) ?_ h6 (h 7 (by decide))
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨hsq, hD⟩, hN⟩

end CertificateChecks.KernelJ4Q

end
