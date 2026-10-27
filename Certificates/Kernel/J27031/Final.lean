module

public import Certificates.Kernel.J27031.ChkR
public import Certificates.Kernel.J27031.V0
public import Certificates.Kernel.J27031.V1
public import Certificates.Kernel.J27031.K
public import Certificates.Kernel.J27031.NA
public import Certificates.Kernel.J27031.Parse
public import Certificates.Kernel.He589203.Final
public import Certificates.Kernel.Sporadic.J2K.Final
public import CFSG.Certificates.Kernel.DcKTSound
public import CFSG.Quasithin.H13.LocDblOdd
public import CFSG.Quasithin.H13.LocDblJ2CheckInputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J27031

open CFSG.KC.DcK CFSG.KC.E64F CFSG.Quasithin.H13.LocDbl CFSG.Quasithin.H13.LocDbl.DcNative
open CFSG.Quasithin.H13.LocDbl.J2Cert CFSG.KC.LQT.BT
open CFSG.QuasithinUnique.K1.SporadicPerm (tab act act_eq slpTabsA slpValidAux j2Prog j2Qp j2ta
  j2tb j2_tab_a j2_tab_b)

theorem inv_all : ∀ c ∈ NA.invPairs, ∀ p < 315, im c.2 (im c.1 p) = p ∧ im c.1 (im c.2 p) = p ∧
    im c.1 p < 315 ∧ im c.2 p < 315 := by
  intro c hc p hp
  have h := List.all_eq_true.1 (List.all_eq_true.1 NA.inv_ok c hc) p (List.mem_range.2 hp)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem ab_lt : ∀ l < 4, ∀ p < 315, ab l p < 315
  | 0, _, p, hp => (inv_all (abc 0, P.TF 0) (by simp [NA.invPairs]) p hp).2.2.1
  | 1, _, p, hp => (inv_all (abc 1, P.TF 1) (by simp [NA.invPairs]) p hp).2.2.1
  | 2, _, p, hp => (inv_all (abc 0, P.TF 0) (by simp [NA.invPairs]) p hp).2.2.2
  | 3, _, p, hp => (inv_all (abc 1, P.TF 1) (by simp [NA.invPairs]) p hp).2.2.2
  | _ + 4, h, _, _ => absurd h (by omega)

theorem good_ofFn {n : Nat} {f : Nat → Nat} (hf : ∀ p < n, f p < n) :
    Good n (Array.ofFn (n := n) fun i => f i.val) f :=
  ⟨Array.size_ofFn, fun p hp => ⟨by simp [Array.getD_eq_getD_getElem?, hp], hf p hp⟩⟩

@[expose] noncomputable def AB3 : Array (Array Nat) :=
  #[Array.ofFn (n := 315) fun i => ab 0 i.val, Array.ofFn (n := 315) fun i => ab 1 i.val,
    Array.ofFn (n := 315) fun i => ab 2 i.val, Array.ofFn (n := 315) fun i => ab 3 i.val]

@[expose] noncomputable def RT3 : Array (Array Nat) :=
  (qn.map fun i => (slpTabsA (AB3.getD 0 #[]) (AB3.getD 1 #[]) j2Prog)[i]!).toArray

@[expose] noncomputable def D7 : DcData where
  n := 315
  B := BK
  AB := AB3
  RT := RT3
  RTi := RT3.map invTab
  NR := 128
  rpar := (bfsEnumL 315 BK RT3 200).1
  rlab := (bfsEnumL 315 BK RT3 200).2
  lb := orbitLabels 315 RT3
  reps := parseWords repsStr
  edges := parseEdges edgesStr
  c0 := root
  inEdge := parseNats inEdgeStr
  dIn := parseNats dInStr
  reach := (parseNats reachStr).toList
  outEdge := parseNats outEdgeStr
  dOut := parseNats dOutStr
  Vs := vData.map fun V =>
    let e := bfsEnumL 315 BK (RT3 ++ (V.1.map (tabW 315 AB3)).toArray) (V.2 + 10)
    (V.1, e.1, e.2, V.2)
  order := 604800

theorem AB3_get : ∀ l < 4, AB3.getD l #[] = Array.ofFn (n := 315) fun i => ab l i.val
  | 0, _ => by simp only [AB3, Array.getD_eq_getD_getElem?, List.getElem?_toArray]; rfl
  | 1, _ => by simp only [AB3, Array.getD_eq_getD_getElem?, List.getElem?_toArray]; rfl
  | 2, _ => by simp only [AB3, Array.getD_eq_getD_getElem?, List.getElem?_toArray]; rfl
  | 3, _ => by simp only [AB3, Array.getD_eq_getD_getElem?, List.getElem?_toArray]; rfl
  | _ + 4, h => absurd h (by omega)

theorem ab_good (l : Nat) (hl : l < 4) : Good 315 (AB3.getD l #[]) (ab l) := by
  rw [AB3_get l hl]
  exact good_ofFn (ab_lt l hl)

theorem slp_rep {ta tb : Array Nat} {prog : List (Nat × Nat)} {TF : Nat → Nat} {K : Nat}
    (ha : CFSG.KC.LQT.BW.Pf.Rep 315 14 (TF 0) ta) (hb : CFSG.KC.LQT.BW.Pf.Rep 315 14 (TF 1) tb)
    (hv : slpValidAux prog 2 = true)
    (hnd : ∀ c < K, nodesT 315 14 prog TF (c * 8) 8 = true) (hK : prog.length + 2 ≤ K * 8) :
    ∀ j < prog.length + 2, CFSG.KC.LQT.BW.Pf.Rep 315 14 (TF j) (slpTabsA ta tb prog)[j]! := by
  intro j hj
  have hs : (slpTabsA ta tb prog).size = prog.length + 2 := by
    rw [slpTabsA, CFSG.KC.LQT.BS.Pf.foldl_slpStepA_size]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega
  rw [slpTabsA]
  refine CFSG.KC.LQT.BS.Pf.slpTF_rep prog #[ta, tb] (fun i hi => ?_) hv
    (fun q hq => CFSG.KD.He589203.nodes_eq hnd hK q hq) j (by rw [← slpTabsA, hs]; exact hj)
  rcases i with _ | _ | i
  · exact ha
  · exact hb
  · simp at hi

theorem valid : slpValidAux j2Prog 2 = true := by decide

theorem slp3_rep : ∀ j < j2Prog.length + 2,
    CFSG.KC.LQT.BW.Pf.Rep 315 14 (S.TF j)
      (slpTabsA (AB3.getD 0 #[]) (AB3.getD 1 #[]) j2Prog)[j]! :=
  slp_rep (K := 25)
    (CFSG.KD.He589203.rep_of_good (c := S.TF 0) (t := AB3.getD 0 #[]) (ab_good 0 (by omega)))
    (CFSG.KD.He589203.rep_of_good (c := S.TF 1) (t := AB3.getD 1 #[]) (ab_good 1 (by omega)))
    valid
    (fun c hc => List.all_eq_true.1 NA.nodes c (List.mem_range.2 hc))
    (by decide)

theorem rt_size : RT3.size = 3 := rfl

theorem rt_good : ∀ t < 3, Good 315 (RT3.getD t #[]) (rt t)
  | 0, _ => CFSG.KD.He7149.good_of_rep (slp3_rep 155 (by decide))
  | 1, _ => CFSG.KD.He7149.good_of_rep (slp3_rep 166 (by decide))
  | 2, _ => CFSG.KD.He7149.good_of_rep (slp3_rep 179 (by decide))
  | _ + 3, h => absurd h (by omega)

theorem rti_good : ∀ t < 3, Good 315 ((RT3.map invTab).getD t #[]) (rti t) := by
  intro t ht
  have hc : (rtc t, P.TF (t + 2)) ∈ NA.invPairs := by
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;> simp [NA.invPairs]
  have hi := inv_all _ hc
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem (by rw [rt_size]; exact ht)]
  have h := rt_good t ht
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [rt_size]; exact ht)] at h
  exact invTab_good h (fun p hp => (hi p hp).2.2.2) (fun p hp => (hi p hp).1)
    (fun p hp => (hi p hp).2.1)

theorem rt_all : ∀ t < RT3.size, Good 315 (RT3.getD t #[]) (rt t) := fun t ht =>
  rt_good t (by rw [rt_size] at ht; exact ht)

theorem r_all : ∀ k < 128, elemK 315 BK rt 3 ER k = true := fun k hk =>
  CFSG.KD.He589203.elems_all r_el k (Nat.zero_le _) (by omega)

theorem rpar_eq : bfsEnumL 315 BK RT3 200 =
    (((List.range 128).map ER.par).toArray, ((List.range 128).map ER.lab).toArray) :=
  bfsEnumL_of_elemK rt_all (by decide) r_hd r_all

theorem slices2 {G : Nat → Nat → Nat} {E : EnumK} {h : Nat}
    (h0 : elemsK 315 BK G 4 E 0 h = true) (h1 : elemsK 315 BK G 4 E h h = true) :
    ∀ k < 2 * h, elemK 315 BK G 4 E k = true := by
  intro k hk
  rcases Nat.lt_or_ge k h with a | a
  · exact CFSG.KD.He589203.elems_all h0 k (by omega) (by omega)
  · exact CFSG.KD.He589203.elems_all h1 k a (by omega)

theorem vg_good {ws : List (List Nat)} (hw : ∀ w ∈ ws, ∀ l ∈ w, l < 4) :
    ∀ t < (RT3 ++ (ws.map (tabW 315 AB3)).toArray).size,
      Good 315 ((RT3 ++ (ws.map (tabW 315 AB3)).toArray).getD t #[]) (K.vg (exOf ab ws) t) := by
  intro t ht
  rcases Nat.lt_or_ge t 3 with h3 | h3
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by rw [rt_size]; exact h3),
      ← Array.getD_eq_getD_getElem?]
    have e : K.vg (exOf ab ws) t = rt t := by simp [DcK.vg, K, h3]
    rw [e]
    exact rt_good t h3
  · simp only [Array.size_append, rt_size, List.size_toArray, List.length_map] at ht
    have hi : t - 3 < ws.length := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by rw [rt_size]; exact h3)]
    simp only [rt_size, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some]
    have e : K.vg (exOf ab ws) t = wordF ab ws[t - 3] := by
      simp [DcK.vg, K, exOf, show ¬ (t < 3) from by omega, List.getD_eq_getElem?_getD, hi]
    rw [e]
    exact good_tabW fun l hl => ab_good l (hw _ (List.getElem_mem hi) l hl)

theorem v0_all : ∀ k < 1152, elemK 315 BK (K.vg (exOf ab w0)) 4 EV0 k = true :=
  slices2 (h := 576) CV0.s0 CV0.s1

theorem v1_all : ∀ k < 1920, elemK 315 BK (K.vg (exOf ab w1)) 4 EV1 k = true :=
  slices2 (h := 960) CV1.s0 CV1.s1

theorem vs_eq : D7.Vs = [(w0, ((List.range 1152).map EV0.par).toArray,
      ((List.range 1152).map EV0.lab).toArray, 1152),
    (w1, ((List.range 1920).map EV1.par).toArray, ((List.range 1920).map EV1.lab).toArray,
      1920)] := by
  have e0 := bfsEnumL_of_elemK (vg_good (ws := w0) (by decide)) (by decide) CV0.hd v0_all
  have e1 := bfsEnumL_of_elemK (vg_good (ws := w1) (by decide)) (by decide) CV1.hd v1_all
  have e : D7.Vs = [(w0, (bfsEnumL 315 BK (RT3 ++ (w0.map (tabW 315 AB3)).toArray) 1162).1,
      (bfsEnumL 315 BK (RT3 ++ (w0.map (tabW 315 AB3)).toArray) 1162).2, 1152),
    (w1, (bfsEnumL 315 BK (RT3 ++ (w1.map (tabW 315 AB3)).toArray) 1930).1,
      (bfsEnumL 315 BK (RT3 ++ (w1.map (tabW 315 AB3)).toArray) 1930).2, 1920)] := rfl
  rw [e, e0, e1]
  rfl

theorem rel : Rel D7 K := by
  have hp := parse_ok
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨pe, pi⟩, pd⟩, pr⟩, po⟩, pdo⟩ := hp
  refine
    { n_eq := rfl, B_eq := rfl, ab_size := rfl, ab := ab_good, rt_size := rt_size
      rti_size := by
        change (RT3.map invTab).size = 3
        rw [Array.size_map, rt_size]
      rt := rt_good
      rti := rti_good
      NR_eq := rfl
      rpar := fun k hk => by
        change (bfsEnumL 315 BK RT3 200).1.getD k 0 = ER.par k
        rw [rpar_eq]; exact CFSG.KD.He589203.getD_range_map _ hk
      rlab := fun k hk => by
        change (bfsEnumL 315 BK RT3 200).2.getD k 0 = ER.lab k
        rw [rpar_eq]; exact CFSG.KD.He589203.getD_range_map _ hk
      lb := fun q hq => orbitLabels_of_orbCK rt_all r_orb q hq
      reps_eq := by
        change parseWords repsStr = _
        rw [T.reps.eq, parseWords_ofList]; rfl
      edges_eq := by
        change parseEdges edgesStr = _
        rw [T.edges.eq, parseEdges_ofList (CFSG.KD.He589203.some_getD pe [])]; rfl
      c0_eq := rfl
      inEdge_eq := by
        change parseNats inEdgeStr = _
        rw [T.inEdge.eq, parseNats_ofList (CFSG.KD.He589203.some_getD pi [])]; rfl
      dIn_eq := by
        change parseNats dInStr = _
        rw [T.dIn.eq, parseNats_ofList (CFSG.KD.He589203.some_getD pd [])]; rfl
      reach_eq := by
        change (parseNats reachStr).toList = _
        rw [T.reach.eq, parseNats_ofList (CFSG.KD.He589203.some_getD pr [])]; rfl
      outEdge_eq := by
        change parseNats outEdgeStr = _
        rw [T.outEdge.eq, parseNats_ofList (CFSG.KD.He589203.some_getD po [])]; rfl
      dOut_eq := by
        change parseNats dOutStr = _
        rw [T.dOut.eq, parseNats_ofList (CFSG.KD.He589203.some_getD pdo [])]; rfl
      order_eq := rfl
      Vs := by
        rw [vs_eq]
        refine List.Forall₂.cons ⟨rfl, rfl, fun i hi p _ => rfl, fun k hk => ?_⟩
          (List.Forall₂.cons ⟨rfl, rfl, fun i hi p _ => rfl, fun k hk => ?_⟩ List.Forall₂.nil)
        · exact ⟨CFSG.KD.He589203.getD_range_map _ hk, CFSG.KD.He589203.getD_range_map _ hk⟩
        · exact ⟨CFSG.KD.He589203.getD_range_map _ hk, CFSG.KD.He589203.getD_range_map _ hk⟩ }

theorem all63 {f : Nat → Bool} (h : ∀ c < 7, (List.range' (9 * c) 9).all f = true) :
    (List.range 63).all f = true := by
  refine List.all_eq_true.2 fun i hi => ?_
  have hi := List.mem_range.1 hi
  exact List.all_eq_true.1 (h (i / 9) (by omega)) i (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem chkK : chkAllKT K IV HitV PN xt xti = true := by
  have hs := CK.size
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨hsz, hiv⟩, hhv⟩ := hs
  have hd : K.distOKNT xt xti IV PN = true := by
    unfold DcK.distOKNT
    rw [CK.invs, hsz, hiv]
    have h := all63 (f := fun i => (List.range K.reps.size).all fun j =>
      decide (j ≤ i) || IV.getD i 0 != IV.getD j 0 || K.noHitKT xt xti i j (PN i j))
      fun c hc => by
        interval_cases c
        exacts [CK.d0, CK.d1, CK.d2, CK.d3, CK.d4, CK.d5, CK.d6]
    rw [hsz] at h
    simp only [h, beq_self_eq_true, Bool.and_self]
  have hh : K.hitOKT xt xti HitV = true := by
    unfold DcK.hitOKT
    rw [hsz, hhv]
    have h := all63 (f := fun j => K.hitT xt xti j == some (HitV.getD j 0)) fun c hc => by
      interval_cases c
      exacts [CK.h0, CK.h1, CK.h2, CK.h3, CK.h4, CK.h5, CK.h6]
    simp only [h, beq_self_eq_true, Bool.and_self]
  have ht : K.tabsOK xt xti 0 K.reps.size = true := by
    rw [hsz]
    unfold DcK.tabsOK
    refine List.all_eq_true.2 fun j hj => ?_
    have hj := List.mem_range'_1.1 hj
    rcases Nat.lt_or_ge j 21 with a | a
    · exact List.all_eq_true.1 CK.t0 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    rcases Nat.lt_or_ge j 42 with b | b
    · exact List.all_eq_true.1 CK.t1 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    · exact List.all_eq_true.1 CK.t2 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  unfold chkAllKT
  rw [CK.inv, CK.basic, CK.lab, hd, CK.edges, CK.vs, hh, CK.mass, ht]
  rfl

theorem D7_chkAll : D7.chkAll = true := by
  refine chkAll_of_chkAllKT rel r_all (fun V hV k hk => ?_) chkK
  simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hV
  rcases hV with rfl | rfl
  · exact v0_all k hk
  · exact v1_all k hk

open CFSG.Sporadic.J2 in
theorem base3 :
    ∀ g : J, (∀ p ∈ D7.B, act 315 g p = p) → g = 1 := by
  intro g hg
  have hfix : ∀ i < 3,
      CFSG.Sporadic.Th.idx 315 g Native.chainBase[i]! = Native.chainBase[i]! := by
    intro i hi
    have hb : Native.chainBase[i]! ∈ D7.B := by
      interval_cases i <;> decide
    have hlt : Native.chainBase[i]! < 315 := by
      interval_cases i <;> decide
    rw [CFSG.Sporadic.Th.idx_of_lt g hlt, ← act_eq g ⟨_, hlt⟩]
    exact hg _ hb
  have hlv : ∀ i ≤ 3, g ∈ lvl i := by
    intro i hi
    induction i with
    | zero => exact mem_lvl_zero g
    | succ i ih =>
      exact (chain_facts'.2.1 i (by rw [chainBase_size]; omega) g (ih (by omega))).1
        (hfix i (by omega))
  have hc : Nat.card (lvl 3) = 1 := by
    rw [chain_facts'.2.2 3 (by rw [chainBase_size]), chainBase_size]
    simp
  have hbot := (Subgroup.card_eq_one).1 hc
  have h3 := hlv 3 le_rfl
  rw [hbot] at h3
  exact (Subgroup.mem_bot).1 h3

open CFSG.Sporadic.J2 in
theorem hta : tab 315 (a : J) = (D7.AB.getD 0 #[]).toList := by
  rw [j2_tab_a]
  change j2ta = (AB3.getD 0 #[]).toList
  rw [AB3_get 0 (by omega)]
  unfold j2ta
  rw [CertificateChecks.KernelSpor.J2K.orb_eq.1]
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, Array.length_toList,
    Array.size_ofFn])
  intro i h1 h2
  have hi : i < 315 := by simpa only [List.length_map, List.length_range] using h1
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getElem_ofFn]
  rw [CertificateChecks.KernelSpor.J2K.al_get hi]
  have h := List.all_eq_true.1 NA.ab_ok i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.1]
  rfl

open CFSG.Sporadic.J2 in
theorem htb : tab 315 (b : J) = (D7.AB.getD 1 #[]).toList := by
  rw [j2_tab_b]
  change j2tb = (AB3.getD 1 #[]).toList
  rw [AB3_get 1 (by omega)]
  unfold j2tb
  rw [CertificateChecks.KernelSpor.J2K.orb_eq.1]
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, Array.length_toList,
    Array.size_ofFn])
  intro i h1 h2
  have hi : i < 315 := by simpa only [List.length_map, List.length_range] using h1
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getElem_ofFn]
  rw [CertificateChecks.KernelSpor.J2K.be_get hi]
  have h := List.all_eq_true.1 NA.ab_ok i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.2]
  rfl

theorem orders : D7.Vs.map (·.2.2.2) = [1152, 1920] := by
  rw [vs_eq]
  rfl

theorem sq : ∀ V ∈ D7.Vs, (V.2.2.2.primeFactors.filter fun r => r ^ 2 ∣ V.2.2.2).card ≤ 2 := by
  intro V hV
  have hm : V.2.2.2 ∈ D7.Vs.map (·.2.2.2) := List.mem_map_of_mem hV
  rw [orders] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h <;> rw [h] <;> simp [Nat.primeFactors] <;> decide

theorem qn_lt : ∀ i ∈ qn, i < j2Prog.length + 2 := by decide

open CFSG.Sporadic.J2 in
theorem sylowNoDouble : SylowNoDouble ↥J :=
  @sylowNoDouble_of_dc J _ _ D7 (inferInstance : MulAction J (Fin 315)) a b base3 hta htb j2Prog
    valid qn qn_lt rfl card_J 7 rfl (by decide) D7_chkAll sq

open CFSG.Sporadic.J2 in
theorem oddIndexBound : OddIndexBound ↥J [1152, 1920] := by
  have h := @oddIndexBound_of_dc J _ _ D7 (inferInstance : MulAction J (Fin 315)) a b base3 hta
    htb j2Prog valid qn qn_lt rfl card_J 7 rfl (by decide) D7_chkAll
  rw [orders] at h
  exact h

end CFSG.KD.J27031

end
