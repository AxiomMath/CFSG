module

public import Certificates.Kernel.He589208.ChkR
public import Certificates.Kernel.He589208.V0
public import Certificates.Kernel.He589208.V1
public import Certificates.Kernel.He589208.K
public import Certificates.Kernel.He589208.NA
public import Certificates.Kernel.He589208.Parse
public import Certificates.Kernel.He589208.Mem
public import Certificates.Kernel.He589208.Comm
public import Certificates.Kernel.He589203.Final
public import CFSG.Certificates.Kernel.SporSch.PairHeCntSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Quasithin.H13.LocDblOdd

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He589208

open CFSG.KC.DcK CFSG.KC.E64F CFSG.Quasithin.H13.LocDbl CFSG.Quasithin.H13.LocDbl.DcNative
open CFSG.Quasithin.H13.LocDbl.HeC0 CFSG.KC.LQT.BT
open CFSG.QuasithinUnique.K1.SporadicPerm (tab act act_eq tab_getD slpTabsA slpValidAux)
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier hiding tab
open CFSG.Sporadic.HeldB CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

theorem inv_all : ∀ c ∈ NA.invPairs, ∀ p < 8330, im c.2 (im c.1 p) = p ∧ im c.1 (im c.2 p) = p ∧
    im c.1 p < 8330 ∧ im c.2 p < 8330 := by
  intro c hc p hp
  have h := List.all_eq_true.1 (List.all_eq_true.1 NA.inv_ok c hc) p (List.mem_range.2 hp)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem ab_lt : ∀ l < 4, ∀ p < 8330, ab l p < 8330
  | 0, _, p, hp => (inv_all (abc 0, P.TF 0) (by simp [NA.invPairs]) p hp).2.2.1
  | 1, _, p, hp => (inv_all (abc 1, P.TF 1) (by simp [NA.invPairs]) p hp).2.2.1
  | 2, _, p, hp => (inv_all (abc 0, P.TF 0) (by simp [NA.invPairs]) p hp).2.2.2
  | 3, _, p, hp => (inv_all (abc 1, P.TF 1) (by simp [NA.invPairs]) p hp).2.2.2
  | _ + 4, h, _, _ => absurd h (by omega)

theorem good_ofFn {n : Nat} {f : Nat → Nat} (hf : ∀ p < n, f p < n) :
    Good n (Array.ofFn (n := n) fun i => f i.val) f :=
  ⟨Array.size_ofFn, fun p hp => ⟨by simp [Array.getD_eq_getD_getElem?, hp], hf p hp⟩⟩

theorem AB8_get : ∀ l < 4, AB8.getD l #[] = Array.ofFn (n := 8330) fun i => ab l i.val
  | 0, _ => by simp only [AB8, Array.getD_eq_getD_getElem?, List.getElem?_toArray]; rfl
  | 1, _ => by simp only [AB8, Array.getD_eq_getD_getElem?, List.getElem?_toArray]; rfl
  | 2, _ => by simp only [AB8, Array.getD_eq_getD_getElem?, List.getElem?_toArray]; rfl
  | 3, _ => by simp only [AB8, Array.getD_eq_getD_getElem?, List.getElem?_toArray]; rfl
  | _ + 4, h => absurd h (by omega)

theorem ab_good (l : Nat) (hl : l < 4) : Good 8330 (AB8.getD l #[]) (ab l) := by
  rw [AB8_get l hl]
  exact good_ofFn (ab_lt l hl)

theorem slp8_rep : ∀ j < prog.length + 2,
    CFSG.KC.LQT.BW.Pf.Rep 8330 14 (S.TF j)
      (slpTabsA (AB8.getD 0 #[]) (AB8.getD 1 #[]) prog)[j]! :=
  CFSG.KD.He589203.slp_rep (K := 4)
    (CFSG.KD.He589203.rep_of_good (c := S.TF 0) (t := AB8.getD 0 #[]) (ab_good 0 (by omega)))
    (CFSG.KD.He589203.rep_of_good (c := S.TF 1) (t := AB8.getD 1 #[]) (ab_good 1 (by omega)))
    (by decide)
    (fun c hc => by
      rcases c with _ | _ | _ | _ | c
      exacts [NA.n0, NA.n1, NA.n2, NA.n3, absurd hc (by omega)])
    (by decide)

theorem rt_size : RT8.size = 3 := rfl

theorem rt_good : ∀ t < 3, Good 8330 (RT8.getD t #[]) (rt t)
  | 0, _ => CFSG.KD.He7149.good_of_rep (slp8_rep 7 (by decide))
  | 1, _ => CFSG.KD.He7149.good_of_rep (slp8_rep 15 (by decide))
  | 2, _ => CFSG.KD.He7149.good_of_rep (slp8_rep 25 (by decide))
  | _ + 3, h => absurd h (by omega)

theorem rti_good : ∀ t < 3, Good 8330 ((RT8.map invTab).getD t #[]) (rti t) := by
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

theorem rt_all : ∀ t < RT8.size, Good 8330 (RT8.getD t #[]) (rt t) := fun t ht =>
  rt_good t (by rw [rt_size] at ht; exact ht)

theorem r_all : ∀ k < 512, elemK 8330 B rt 3 ER k = true := fun k hk =>
  CFSG.KD.He589203.elems_all r_el k (Nat.zero_le _) (by omega)

theorem rpar_eq : bfsEnumL 8330 B RT8 600 =
    (((List.range 512).map ER.par).toArray, ((List.range 512).map ER.lab).toArray) :=
  bfsEnumL_of_elemK rt_all (by decide) r_hd r_all

theorem slices4 {G : Nat → Nat → Nat} {E : EnumK}
    (h0 : elemsK 8330 B G 4 E 0 1920 = true) (h1 : elemsK 8330 B G 4 E 1920 1920 = true)
    (h2 : elemsK 8330 B G 4 E 3840 1920 = true) (h3 : elemsK 8330 B G 4 E 5760 1920 = true) :
    ∀ k < 7680, elemK 8330 B G 4 E k = true := by
  intro k hk
  rcases Nat.lt_or_ge k 1920 with a | a
  · exact CFSG.KD.He589203.elems_all h0 k (by omega) (by omega)
  rcases Nat.lt_or_ge k 3840 with b | b
  · exact CFSG.KD.He589203.elems_all h1 k a (by omega)
  rcases Nat.lt_or_ge k 5760 with c | c
  · exact CFSG.KD.He589203.elems_all h2 k b (by omega)
  · exact CFSG.KD.He589203.elems_all h3 k c (by omega)

theorem vg_good {ws : List (List Nat)} (hw : ∀ w ∈ ws, ∀ l ∈ w, l < 4) :
    ∀ t < (RT8 ++ (ws.map (tabW 8330 AB8)).toArray).size,
      Good 8330 ((RT8 ++ (ws.map (tabW 8330 AB8)).toArray).getD t #[]) (K.vg (exOf ab ws) t) := by
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

theorem vs_eq : D8.Vs = [(w0, ((List.range 7680).map EV0.par).toArray,
      ((List.range 7680).map EV0.lab).toArray, 7680),
    (w1, ((List.range 7680).map EV1.par).toArray, ((List.range 7680).map EV1.lab).toArray,
      7680)] := by
  have e0 := bfsEnumL_of_elemK (vg_good (ws := w0) (by decide)) (by decide) CV0.hd
    (slices4 CV0.s0 CV0.s1 CV0.s2 CV0.s3)
  have e1 := bfsEnumL_of_elemK (vg_good (ws := w1) (by decide)) (by decide) CV1.hd
    (slices4 CV1.s0 CV1.s1 CV1.s2 CV1.s3)
  have e : D8.Vs = [(w0, (bfsEnumL 8330 B (RT8 ++ (w0.map (tabW 8330 AB8)).toArray) 7690).1,
      (bfsEnumL 8330 B (RT8 ++ (w0.map (tabW 8330 AB8)).toArray) 7690).2, 7680),
    (w1, (bfsEnumL 8330 B (RT8 ++ (w1.map (tabW 8330 AB8)).toArray) 7690).1,
      (bfsEnumL 8330 B (RT8 ++ (w1.map (tabW 8330 AB8)).toArray) 7690).2, 7680)] := rfl
  rw [e, e0, e1]
  rfl

theorem rel : Rel D8 K := by
  have hp := parse_ok
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨pe, pi⟩, pd⟩, pr⟩, po⟩, pdo⟩ := hp
  refine
    { n_eq := rfl, B_eq := rfl, ab_size := rfl, ab := ab_good, rt_size := rt_size
      rti_size := by
        change (RT8.map invTab).size = 3
        rw [Array.size_map, rt_size]
      rt := rt_good
      rti := rti_good
      NR_eq := rfl
      rpar := fun k hk => by
        change (bfsEnumL 8330 B RT8 600).1.getD k 0 = ER.par k
        rw [rpar_eq]; exact CFSG.KD.He589203.getD_range_map _ hk
      rlab := fun k hk => by
        change (bfsEnumL 8330 B RT8 600).2.getD k 0 = ER.lab k
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

theorem chkK : chkAllK K IV HitV = true := by
  unfold chkAllK
  rw [CK.inv, CK.basic, CK.lab, CK.dist, CK.edges, CK.vs, CK.hit, CK.mass]
  rfl

theorem D8_chkAll : D8.chkAll = true := by
  refine chkAll_of_chkAllK rel r_all (fun V hV k hk => ?_) chkK
  simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hV
  rcases hV with rfl | rfl
  · exact slices4 CV0.s0 CV0.s1 CV0.s2 CV0.s3 k hk
  · exact slices4 CV1.s0 CV1.s1 CV1.s2 CV1.s3 k hk

noncomputable abbrev E (F : Nat) : Equiv.Perm (Fin 8330) :=
  nfElt 8330 heStrongArrs heBase.toArray (nfArr 5 F)

theorem E_mem {F : Nat} (hF : nfValidK 5 HeC.LR F = true) :
    E F ∈ heP := by
  rw [heP_eq_originalSubgroup]
  exact nfElt_mem heChainArrays (chainCheckFacts heChain_check.1) heChain_valid.1
    (nfPtT_sound HeTc.tc hF).1

theorem hF : nfValidK 5 HeC.LR (Mem.F 0) = true ∧ nfValidK 5 HeC.LR (Mem.F 1) = true := by
  have h := Mem.kNF
  simp only [Bool.and_eq_true] at h
  exact h

theorem bind_all (l : Nat) (hl : l < 2) : ∀ x < 8330,
    bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (Mem.F l) (S.TF l) x = true := by
  intro x hx
  have hc : ∀ c < 10, Mem.bindB c = true := by
    intro c hc
    interval_cases c
    exacts [Mem.kB0, Mem.kB1, Mem.kB2, Mem.kB3, Mem.kB4, Mem.kB5, Mem.kB6, Mem.kB7, Mem.kB8,
      Mem.kB9]
  have h := CFSG.KC.Misc.Clos.forall_of_chunks 833 10 Mem.bindAt (fun c hc' => hc c hc') x
    (by omega)
  simp only [Mem.bindAt, Bool.and_eq_true] at h
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact h.1
  · exact h.2

theorem E_repF (l : Nat) (hl : l < 2) : RepF 8330 (im (S.TF l)) (E (Mem.F l)) :=
  bind5_spec HeTc.tc (by rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [hF.1, hF.2])
    (bind_all l hl)

theorem hF_of (l : Nat) (hl : l < 2) : nfValidK 5 HeC.LR (Mem.F l) = true := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  exacts [hF.1, hF.2]

theorem gen0_eq : heGen 0 = unpack 8330 14 (HeC.S 0) := by
  have h := He2112.gen_eq 0 (by norm_num)
  rw [heGenArrs, getElem!_pos _ 0 (by simp), Array.getElem_ofFn] at h
  exact h

theorem unpackGet {p x : Nat} (hx : x < 8330) : (unpack 8330 14 p)[x]! = pg 14 (mask 14) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem t0_map (x : Fin 8330) :
    ((heGenPerm 0 x : Fin 8330) : Nat) = t0 x := by
  have h := rep_heGen (k := 0) (by norm_num) x
  rw [← h, gen0_eq, unpackGet x.2]
  rfl

theorem comm_pt (l : Nat) (hl : l < 2) : ∀ x ∈ [0, 1, 2, 3, 4],
    CFSG.KC.LQT.PW.imgW 14 (S.TF l) (t0 x) = t0 (CFSG.KC.LQT.PW.imgW 14 (S.TF l) x) := by
  have hm : S.TF l ∈ [S.TF 0, S.TF 1] := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  intro x hx
  have h := List.all_eq_true.1 (List.all_eq_true.1 comm_ok _ hm) x hx
  exact Nat.eq_of_beq_eq_true h

theorem E_pt (l : Nat) (hl : l < 2) (y : Fin 8330) :
    ((E (Mem.F l) y : Fin 8330) : Nat) = CFSG.KC.LQT.PW.imgW 14 (S.TF l) y.val :=
  (E_repF l hl y.val y.2).symm

theorem E_pt1 (l : Nat) (hl : l < 2) (b : Fin 8330) :
    ((E (Mem.F l) (heGenPerm 0 b) : Fin 8330) : Nat) =
      CFSG.KC.LQT.PW.imgW 14 (S.TF l) (t0 b.val) := by
  rw [E_pt l hl, t0_map]

theorem E_pt2 (l : Nat) (hl : l < 2) (b : Fin 8330) :
    ((heGenPerm 0 (E (Mem.F l) b) : Fin 8330) : Nat) =
      t0 (CFSG.KC.LQT.PW.imgW 14 (S.TF l) b.val) := by
  rw [t0_map, E_pt l hl]

theorem E_base (l : Nat) (hl : l < 2) (b : Fin 8330)
    (hb : (b : Nat) < 5) : (E (Mem.F l) * heGenPerm 0) b = (heGenPerm 0 * E (Mem.F l)) b := by
  apply Fin.ext
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, E_pt1 l hl, E_pt2 l hl]
  exact comm_pt l hl b.val (by simp only [List.mem_cons, List.not_mem_nil]; omega)

theorem E_comm (l : Nat) (hl : l < 2) :
    E (Mem.F l) * heGenPerm 0 = heGenPerm 0 * E (Mem.F l) := by
  have hE := E_mem (hF_of l hl)
  have hτ := heGenPerm_mem (k := 0) (by norm_num)
  have hmem : (heGenPerm 0 * E (Mem.F l))⁻¹ * (E (Mem.F l) * heGenPerm 0) ∈ heP :=
    heP.mul_mem (heP.inv_mem (heP.mul_mem hτ hE)) (heP.mul_mem hE hτ)
  have h1 := eq_one_of_fix_base hmem fun b hb => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact E_base l hl b hb
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem tab_eq_of_rep {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))} (g : ↥A) (arr : Array ℕ)
    (hsz : arr.size = n) (hr : CFSG.Monster.B.Co2.Rep n arr (g : Equiv.Perm (Fin n))) :
    tab n g = arr.toList := by
  apply List.ext_getElem
  · simp [tab, hsz]
  · intro i h1 h2
    have hi : i < n := by simpa [tab] using h1
    have e1 : (tab n g)[i] = (tab n g).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
      rfl
    have e2 : (tab n g).getD i 0 = ((g • (⟨i, hi⟩ : Fin n) : Fin n) : ℕ) := tab_getD g ⟨i, hi⟩
    have h3 := hr ⟨i, hi⟩
    rw [getElem!_pos arr i (by omega)] at h3
    rw [e1, e2]
    simp only [Array.getElem_toList]
    rw [h3]
    rfl

theorem ab_rep (l : Nat) (hl : l < 2) :
    CFSG.Monster.B.Co2.Rep 8330 (AB8.getD l #[]) (E (Mem.F l)) := fun x => by
  have h := E_repF l hl x.val x.2
  simp only [Fin.eta] at h
  rw [AB8_get l (by omega), getElem!_pos _ x.val (by simp), Array.getElem_ofFn, ← h]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rfl
  · rfl

theorem oddIndexBound :
    OddIndexBound ↥(centralizerIn heP (heGenPerm 0)) [7680, 7680] := by
  have hamem : E (Mem.F 0) ∈ centralizerIn heP (heGenPerm 0) :=
    mem_centralizerIn.2 ⟨E_mem (hF_of 0 (by norm_num)), E_comm 0 (by norm_num)⟩
  have hbmem : E (Mem.F 1) ∈ centralizerIn heP (heGenPerm 0) :=
    mem_centralizerIn.2 ⟨E_mem (hF_of 1 (by norm_num)), E_comm 1 (by norm_num)⟩
  set a : ↥(centralizerIn heP (heGenPerm 0)) := ⟨E (Mem.F 0), hamem⟩ with ha
  set b : ↥(centralizerIn heP (heGenPerm 0)) := ⟨E (Mem.F 1), hbmem⟩ with hb
  have hta : tab 8330 a = (D8.AB.getD 0 #[]).toList :=
    tab_eq_of_rep a _ (ab_good 0 (by norm_num)).1 (ab_rep 0 (by norm_num))
  have htb : tab 8330 b = (D8.AB.getD 1 #[]).toList :=
    tab_eq_of_rep b _ (ab_good 1 (by norm_num)).1 (ab_rep 1 (by norm_num))
  have hbase : ∀ g : ↥(centralizerIn heP (heGenPerm 0)), (∀ p ∈ D8.B, act 8330 g p = p) →
      g = 1 := by
    intro g hg
    apply Subtype.ext
    refine eq_one_of_fix_base (mem_centralizerIn.1 g.2).1 fun x hx => ?_
    have h := hg x.val (by simp [D8, B]; omega)
    rw [act_eq g x] at h
    exact Fin.ext h
  have hord : Nat.card ↥(centralizerIn heP (heGenPerm 0)) = D8.order := card_heP_cent0
  have h := @oddIndexBound_of_dc ↥(centralizerIn heP (heGenPerm 0)) _ _ D8
    (inferInstance : MulAction ↥(centralizerIn heP (heGenPerm 0)) (Fin 8330)) a b hbase hta htb
    prog (by decide) qp (by decide) rfl hord 9 rfl (by decide) D8_chkAll
  have hv : D8.Vs.map (fun V => V.2.2.2) = [7680, 7680] := by
    rw [vs_eq]
    rfl
  rw [hv] at h
  exact h

end CFSG.KD.He589208

end
