
module

public import Certificates.Kernel.J4Q.Dec2K
public import Certificates.Kernel.J4Q.C4027P
public import Certificates.Kernel.J4Q.D4Data
public import Certificates.Kernel.J4Q.D2B1
public import Certificates.Kernel.J4Q.D2A8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Native
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Wit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 CFSG.QuasithinUnique.A5

@[expose] noncomputable def anyLK (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def allLK (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def fixK (k n : Nat) : Bool := Nat.beq (vecEtaK rm Us k n) n

@[expose] noncomputable def d4XI : Nat := getN one XG 8

@[expose] noncomputable def d4UsK (r PI : Nat) : List Nat :=
  (fun a1 => (fun a2 => (fun a3 => [vecJ rm a1 PI, vecJ rm a2 PI, vecJ rm a3 PI,
    vecJ rm (vecJ rm a3 d4XI) PI]) (vecJ rm a2 d4XI)) (vecJ rm a1 d4XI)) (vecJ rm r d4XI)

@[expose] noncomputable def d4UL (i : Nat) : List Nat :=
  [getN 0 D4U (Nat.mul 4 i), getN 0 D4U (Nat.add (Nat.mul 4 i) 1), getN 0 D4U (Nat.add (Nat.mul 4 i) 2),
    getN 0 D4U (Nat.add (Nat.mul 4 i) 3)]

@[expose] noncomputable def d4FL (i : Nat) : List Nat :=
  smapK (fun j => getN 0 D4F (Nat.add (Nat.mul 14 i) j)) (rangeK 14)

@[expose] noncomputable def d4RepK (i : Nat) : Bool :=
  (fun r P PI => andB (Nat.beq r (v2N (d4Reps[i]!)))
    (andB (Nat.beq P (wordJ c rm one G5 G5i (d4El (d4Words.getD i []))))
      (andB (Nat.beq PI (wordJ c rm one G5 G5i (invWord (d4El (d4Words.getD i [])))))
        (andB (Nat.beq (vecJ rm (v2N rootV) P) r)
          (andB (eqLK (d4UsK r PI) (d4UL i)) (eqLK (smapK (fun p => vecJ rm p PI) XPTS) (d4FL i)))))))
    (getN 0 D4R i) (getN one D4P i) (getN one D4PI i)

@[expose] noncomputable def d4CellK (i k : Nat) : Bool :=
  orB (notB (andB (notB (Nat.beq k 0)) (allLK (fixK k) (d4UL i))))
    (orB (anyLK (fixK k) (d4FL i)) (anyLK (Nat.beq (Nat.add (Nat.mul 2048 i) k)) D4H))

@[expose] noncomputable def d4LK (t : Nat) : Bool :=
  allR 256 fun j => d4CellK (Nat.div t 8) (Nat.add (Nat.mul 256 (Nat.mod t 8)) j)

@[expose] noncomputable def d4TP (t0 t1 t2 t3 : Nat) : List (Nat × Nat) := [(0, t0), (1, t1), (2, t2), (3, t3)]

@[expose] noncomputable def d4SK (t0 t1 t2 t3 : Nat) : List Nat :=
  smapK (fun m => selPK c rm (d4TP t0 t1 t2 t3) m one) (rangeK 16)

@[expose] noncomputable def d4ConjK (t0 t1 t2 t3 : Nat) (E : List Nat) (K h : Nat) : Bool :=
  (fun S => andB (Nat.beq (getN one S 0) one)
    (andB (allR 16 fun m => allR 4 fun g =>
        Nat.beq (mulJ c rm (getN one S m) (getN one [t0, t1, t2, t3] g)) (getN one S (Nat.xor m (Nat.pow 2 g))))
      (allR 16 fun m => (fun m' => andB (Nat.blt m' 16)
          (Nat.beq (mulJ c rm K (getN one E m)) (mulJ c rm (getN one S m') K)))
        (getN 0 D4HC (Nat.add (Nat.mul 16 h) m))))) (d4SK t0 t1 t2 t3)

@[expose] noncomputable def cjK (T : Nat) : Nat := mulJ c rm (mulJ c rm d2X T) d4XI

@[expose] noncomputable def esK (j : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (d2Es A8G) (d2Es B1G) (Nat.beq j 0)

@[expose] def witB (i k j n : Nat) : Bool :=
  decide (d4Wit.find? (fun w => w.1 == i && w.2.1 == k) = some (i, k, j, n))

@[expose] noncomputable def d4RestK (i k j n h : Nat) : Bool :=
  (fun T => (fun T1 => (fun T2 => orB (notB (Nat.beq (mulJ c rm T T1) (mulJ c rm T1 T)))
      (orB (notB (Nat.beq (mulJ c rm T T2) (mulJ c rm T2 T)))
        (andB (witB i k j n) (andB (Nat.blt j 2) (andB (Nat.blt n 6720)
          (d4ConjK T T1 T2 (cjK T2) (esK j) (CFSG.KD.X0O.MSF n) h)))))) (cjK T1)) (cjK T))
    (mulJ c rm (mulJ c rm (getN one D4PI i) (etaK c rm one Us k)) (getN one D4P i))

@[expose] noncomputable def d4HK (t : Nat) : Bool :=
  (fun key => andB (Nat.blt key 61440)
    (d4RestK (Nat.div key 2048) (Nat.mod key 2048) (getN 0 D4HJ t) (getN 0 D4HN t) t)) (getN 0 D4H t)

theorem allLK_eq (f : Nat → Bool) : ∀ l : List Nat, allLK f l = l.all f
  | [] => rfl
  | x :: l => by
    change andB (f x) (allLK f l) = _
    rw [andB_eq, allLK_eq f l, List.all_cons]

theorem anyLK_eq (f : Nat → Bool) : ∀ l : List Nat, anyLK f l = l.any f
  | [] => rfl
  | x :: l => by
    change orB (f x) (anyLK f l) = _
    rw [orB_eq'', anyLK_eq f l, List.any_cons]

theorem all_congr_mem {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.all f = l.all g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      all_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem any_congr_mem4 {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.any f = l.any g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self,
      any_congr_mem4 fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem all_map_v2N {l : List V2} {g : Nat → Bool} : l.all (fun u => g (v2N u)) = (l.map v2N).all g := by
  rw [List.all_map]
  rfl

theorem any_map_v2N {l : List V2} {g : Nat → Bool} : l.any (fun u => g (v2N u)) = (l.map v2N).any g := by
  rw [List.any_map]
  rfl

theorem bool3 {a b w r : Bool} (h : (!a || (!b || w)) = true) (hr : w = true → r = true) :
    (!a || !b || r) = true := by
  cases a <;> cases b <;> simp_all

theorem cell3 {s f h r : Bool} (hc : (!s || (f || h)) = true) (hr : h = true → r = true) :
    (!s || (f || r)) = true := by
  cases s <;> cases f <;> simp_all

theorem etaE_enc (m : Nat) : WfA (etaE m) ∧ encR (etaE m) = etaK c rm one Us m := eta_enc m

theorem d4EtaTabs_get' {k : Nat} (hk : k < 2048) : d4EtaTabs[k]! = frTable (etaE k) := by
  unfold d4EtaTabs
  rw [getElem!_pos _ k (by simp [hk])]
  simp

theorem fix_eq {u : V2} (hu : u.wf = true) {k : Nat} (hk : k < 2048) : d4Fix k u = fixK k (v2N u) := by
  have h := etaVec_enc hu k
  unfold d4Fix fixK
  rw [d4EtaTabs_get' hk, beq_v2N]
  unfold etaE
  rw [h.2]

theorem conj_enc {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t) :
    WfA (d4Conj T) ∧ encR (d4Conj T) = cjK t :=
  mul_enc hK (mul_enc hK (x0Gen_enc (i := 0) (by decide)) hT) (x0Inv_enc (i := 0) (by decide))

theorem bne_zero (k : Nat) : (k != 0) = notB (Nat.beq k 0) := by
  rw [notB_eq]
  cases h : Nat.beq k 0
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem d4pts_k : eqLK (List.eraseDups xPV) XPTS = true := by quickRfl

theorem d4pts_map : d4Pts.map v2N = XPTS := by
  unfold d4Pts
  rw [← eraseDups_map_inj (f := v2N) _ x0Pts (le_refl _) (fun a _ b _ h => v2N_inj h), pts_map]
  exact eqLK_spec d4pts_k

theorem d4pts_wf : ∀ p ∈ d4Pts, p.wf = true := fun p hp =>
  pts_wf p (List.mem_eraseDups.1 hp)

structure RepEnc (i : Nat) : Prop where
  hP : WfA (wR (d4El (d4Words.getD i []))) ∧ encR (wR (d4El (d4Words.getD i []))) = getN one D4P i
  hPi : WfA (wR (invWord (d4El (d4Words.getD i [])))) ∧
    encR (wR (invWord (d4El (d4Words.getD i [])))) = getN one D4PI i
  hr : getN 0 D4R i = v2N (d4Reps[i]!)
  hroot : vecJ rm (v2N rootV) (getN one D4P i) = getN 0 D4R i
  hu : d4UsK (getN 0 D4R i) (getN one D4PI i) = d4UL i
  hf : (smapK (fun p => vecJ rm p (getN one D4PI i)) XPTS) = d4FL i

theorem repEnc_of {i : Nat} (h : d4RepK i = true) : RepEnc i := by
  unfold d4RepK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true h2).symm⟩,
    ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true h3).symm⟩, Nat.eq_of_beq_eq_true h1,
    Nat.eq_of_beq_eq_true h4, eqLK_spec h5, eqLK_spec h6⟩

theorem us_map {r : V2} (hr : r.wf = true) {Pi : Array V2} {pin : Nat} (hPi : WfA Pi ∧ encR Pi = pin) :
    (∀ u ∈ d4Us r Pi, u.wf = true) ∧ (d4Us r Pi).map v2N = d4UsK (v2N r) pin := by
  have hX := x0Inv_enc (i := 0) (by decide)
  have e : ∀ v : V2, v.wf = true →
      v2N (frApply (frTable (x0InvRows[0]!)) v) = vecJ rm (v2N v) d4XI := fun v hv => by
    rw [v2N_frApply hK hX.1 hv, hX.2]
    rfl
  have w := fun v => wf_frApply hX.1 v
  have ep : ∀ v : V2, v.wf = true → v2N (frApply (frTable Pi) v) = vecJ rm (v2N v) pin := fun v hv => by
    rw [v2N_frApply hK hPi.1 hv, hPi.2]
  unfold d4Us d4UsK
  dsimp only
  refine ⟨?_, ?_⟩
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> exact wf_frApply hPi.1 _
  · simp only [List.map_cons, List.map_nil]
    rw [ep _ (w _), ep _ (w _), ep _ (w _), ep _ (w _)]
    repeat rw [e _ (w _)]
    rw [e _ hr]

theorem stab_eq {i : Nat} (hR : RepEnc i) (hr : (d4Reps[i]!).wf = true) {k : Nat} (hk : k < 2048) :
    (d4Us (d4Reps[i]!) (wR (invWord (d4El (d4Words.getD i []))))).all (d4Fix k) =
      allLK (fixK k) (d4UL i) := by
  obtain ⟨hw, hm⟩ := us_map hr hR.hPi
  rw [all_congr_mem fun u hu => fix_eq (hw u hu) hk, all_map_v2N, hm, ← hR.hr, hR.hu, allLK_eq]

theorem pts_eq {i : Nat} (hR : RepEnc i) {k : Nat} (hk : k < 2048) :
    (d4Pts.map (frApply (frTable (wR (invWord (d4El (d4Words.getD i []))))))).any (d4Fix k) =
      anyLK (fixK k) (d4FL i) := by
  have hw : ∀ u ∈ d4Pts.map (frApply (frTable (wR (invWord (d4El (d4Words.getD i [])))))), u.wf = true :=
    fun u hu => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hu
      exact wf_frApply hR.hPi.1 p
  have hm : (d4Pts.map (frApply (frTable (wR (invWord (d4El (d4Words.getD i []))))))).map v2N = d4FL i := by
    rw [← hR.hf, smapK_eq, ← d4pts_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro p hp
    change v2N (frApply _ p) = vecJ rm (v2N p) _
    rw [v2N_frApply hK hR.hPi.1 (d4pts_wf p hp), hR.hPi.2]
  rw [any_congr_mem4 fun u hu => fix_eq (hw u hu) hk, any_map_v2N, hm, anyLK_eq]

theorem sub_enc {T0 T1 T2 T3 : Array V2} {t0 t1 t2 t3 : Nat} (h0 : WfA T0 ∧ encR T0 = t0)
    (h1 : WfA T1 ∧ encR T1 = t1) (h2 : WfA T2 ∧ encR T2 = t2) (h3 : WfA T3 ∧ encR T3 = t3) (m : Nat) :
    WfA (d4Sub [T0, T1, T2, T3] m) ∧ encR (d4Sub [T0, T1, T2, T3] m) = selPK c rm (d4TP t0 t1 t2 t3) m one := by
  have e : d4Sub [T0, T1, T2, T3] m =
      selRows (fun j => [T0, T1, T2, T3].getD j #[]) m ((d4TP t0 t1 t2 t3).map Prod.fst) (idRows ()) := rfl
  have h := enc_selRows hK (fun j => [T0, T1, T2, T3].getD j #[]) m (d4TP t0 t1 t2 t3) (by
    intro p hp
    simp only [d4TP, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3) (idRows ()) wf_idRows
  rw [enc_idRows hK] at h
  rw [e]
  exact h

theorem sk_get (t0 t1 t2 t3 : Nat) {m : Nat} (hm : m < 16) :
    getN one (d4SK t0 t1 t2 t3) m = selPK c rm (d4TP t0 t1 t2 t3) m one := by
  rw [d4SK, smapK_eq, rangeK_eq, getN_map_range _ _ hm]

theorem conj_of {T0 T1 T2 T3 : Array V2} {t0 t1 t2 t3 : Nat} (h0 : WfA T0 ∧ encR T0 = t0)
    (h1 : WfA T1 ∧ encR T1 = t1) (h2 : WfA T2 ∧ encR T2 = t2) (h3 : WfA T3 ∧ encR T3 = t3)
    {E : Array (Array V2)} {Es : List Nat} (hE : ∀ m < 16, WfA (E[m]!) ∧ encR (E[m]!) = getN one Es m)
    {K : Array V2} {kn : Nat} (hKm : WfA K ∧ encR K = kn) {h : Nat}
    (hc : d4ConjK t0 t1 t2 t3 Es kn h = true) : d4ConjOK [T0, T1, T2, T3] E K = true := by
  have hS := sub_enc h0 h1 h2 h3
  have hts : ∀ g < 4, WfA ([T0, T1, T2, T3].getD g #[]) ∧
      encR ([T0, T1, T2, T3].getD g #[]) = getN one [t0, t1, t2, t3] g := by
    intro g hg
    rcases g with _ | _ | _ | _ | g
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · omega
  have hG : ∀ m < 16, ((List.range 16).map (d4Sub [T0, T1, T2, T3])).getD m #[] = d4Sub [T0, T1, T2, T3] m :=
    fun m hm => by simp [hm]
  have hmem : ∀ m < 16, d4Sub [T0, T1, T2, T3] m ∈ (List.range 16).map (d4Sub [T0, T1, T2, T3]) :=
    fun m hm => List.mem_map_of_mem (List.mem_range.2 hm)
  unfold d4ConjK at hc
  beta_reduce at hc
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨c1, c2, c3⟩ := hc
  unfold d4ConjOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hG 0 (by decide), eqRows_of (hS 0) (id_enc hK)]
    rw [sk_get t0 t1 t2 t3 (by decide : 0 < 16)] at c1
    exact c1
  · refine List.all_eq_true.2 fun m hm => List.all_eq_true.2 fun g hg => ?_
    have hm' := List.mem_range.1 hm
    have hg' := List.mem_range.1 hg
    have hx : Nat.xor m (Nat.pow 2 g) < 16 := xor_lt16 hm' (pow2_lt16 hg')
    refine List.any_eq_true.2 ⟨_, hmem _ hx, ?_⟩
    have k := allR_spec (allR_spec c2 m hm') g hg'
    beta_reduce at k
    rw [sk_get t0 t1 t2 t3 hm', sk_get t0 t1 t2 t3 hx] at k
    rw [hG m hm', eqRows_of (mul_enc hK (hS m) (hts g hg')) (hS _)]
    exact k
  · refine List.all_eq_true.2 fun m hm => ?_
    have hm' := List.mem_range.1 hm
    have k := allR_spec c3 m hm'
    beta_reduce at k
    rw [andB_eq, Bool.and_eq_true] at k
    have hx := lt_of_blt k.1
    refine List.any_eq_true.2 ⟨_, hmem _ hx, ?_⟩
    have k2 := k.2
    rw [sk_get t0 t1 t2 t3 hx] at k2
    rw [eqRows_of (mul_enc hK hKm (hE m hm')) (mul_enc hK (hS _) hKm)]
    exact k2

theorem es_enc {j : Nat} (hj : j < 2) : ∀ m < 16,
    WfA ((([b1344Words, a85Words].map Dec2.eTab).getD j #[])[m]!) ∧
      encR ((([b1344Words, a85Words].map Dec2.eTab).getD j #[])[m]!) = getN one (esK j) m := by
  intro m hm
  rcases j with _ | _ | j
  · exact eTab_enc b1344Words B1G b1_hG hm
  · exact eTab_enc a85Words A8G a8_hG hm
  · omega

theorem rest_of (hR : ∀ i < 30, d4RepK i = true) {t i k : Nat} (hkey : getN 0 D4H t = 2048 * i + k)
    (hk : k < 2048) (ht : d4HK t = true) :
    d4Rest d4Wit ([b1344Words, a85Words].map Dec2.eTab) i k
      (mulRows (mulRows (wR (invWord (d4El (d4Words.getD i [])))) (etaE k)) (wR (d4El (d4Words.getD i [])))) =
        true := by
  simp only [d4HK, andB_eq, Bool.and_eq_true] at ht
  obtain ⟨hb, hr⟩ := ht
  have e1 : Nat.div (getN 0 D4H t) 2048 = i := by
    change getN 0 D4H t / 2048 = i
    omega
  have e2 : Nat.mod (getN 0 D4H t) 2048 = k := by
    change getN 0 D4H t % 2048 = k
    omega
  have hi : i < 30 := by
    have := lt_of_blt hb
    omega
  rw [e1, e2] at hr
  have hE := repEnc_of (hR i hi)
  have hT := mul_enc hK (mul_enc hK hE.hPi (etaE_enc k)) hE.hP
  have hT1 := conj_enc hT
  have hT2 := conj_enc hT1
  have hT3 := conj_enc hT2
  unfold d4RestK at hr
  dsimp only at hr
  unfold d4Rest
  rw [eqRows_of (mul_enc hK hT hT1) (mul_enc hK hT1 hT), eqRows_of (mul_enc hK hT hT2) (mul_enc hK hT2 hT)]
  simp only [orB_eq'', notB_eq] at hr
  refine bool3 hr fun hr => ?_
  rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hr
  obtain ⟨hw, hj, hn, hc⟩ := hr
  have hw' := of_decide_eq_true hw
  rw [hw']
  have hj' := lt_of_blt hj
  have hn' := lt_of_blt hn
  obtain ⟨-, hmap, hwf⟩ := x0Orb_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hj', hn'⟩, conj_of hT hT1 hT2 hT3 (es_enc hj') (mats_get hmap hwf hn') hc⟩

theorem rep_of (hR : ∀ i < 30, d4RepK i = true) (hL : ∀ i < 30, ∀ k < 2048, d4CellK i k = true)
    (hH : ∀ t < 112, d4HK t = true) (hwf : ∀ i < 30, (d4Reps[i]!).wf = true) {i : Nat} (hi : i < 30) :
    d4RepOK d4Wit ([b1344Words, a85Words].map Dec2.eTab) i (d4Reps[i]!) (d4Words.getD i []) = true := by
  have hE := repEnc_of (hR i hi)
  unfold d4RepOK
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨hwf i hi, wf_bool hE.hP.1⟩, wf_bool hE.hPi.1⟩, ?_⟩, ?_⟩
  · rw [beq_v2N, v2N_frApply hK hE.hP.1 rootV_wf', hE.hP.2, hE.hroot, hE.hr]
    exact Nat.beq_refl _
  · unfold d4Estab
    rw [List.all_filter]
    refine List.all_eq_true.2 fun k hk => ?_
    have hk' := List.mem_range.1 hk
    have hc := hL i hi k hk'
    unfold d4CellK at hc
    unfold d4PairOK
    rw [stab_eq hE (hwf i hi) hk', pts_eq hE hk', bne_zero, notB_eq]
    simp only [orB_eq'', notB_eq, andB_eq] at hc
    refine cell3 hc fun h => ?_
    rw [anyLK_eq, List.any_eq_true] at h
    obtain ⟨x, hx, hb⟩ := h
    obtain ⟨t, ht, rfl⟩ := getN_of_mem 0 hx
    have hkey : getN 0 D4H t = 2048 * i + k := (Nat.eq_of_beq_eq_true hb).symm
    have hlen : D4H.length = 112 := rfl
    exact rest_of hR hkey hk' (hH t (hlen ▸ ht))

theorem cells_of (h : ∀ t < 240, d4LK t = true) : ∀ i < 30, ∀ k < 2048, d4CellK i k = true := by
  intro i hi k hk
  have ht : 8 * i + k / 256 < 240 := by omega
  have h1 := allR_spec (h _ ht) (k % 256) (Nat.mod_lt _ (by decide))
  have e1 : Nat.div (8 * i + k / 256) 8 = i := by
    change (8 * i + k / 256) / 8 = i
    omega
  have e2 : Nat.add (Nat.mul 256 (Nat.mod (8 * i + k / 256) 8)) (k % 256) = k := by
    change 256 * ((8 * i + k / 256) % 8) + k % 256 = k
    omega
  beta_reduce at h1
  rw [e1, e2] at h1
  exact h1

theorem reps_wf : ∀ i < 30, (d4Reps[i]!).wf = true := by decide

theorem d4_of (hR : ∀ i < 30, d4RepK i = true) (hL : ∀ i < 30, ∀ k < 2048, d4CellK i k = true)
    (hH : ∀ t < 112, d4HK t = true) (hwf : ∀ i < 30, (d4Reps[i]!).wf = true) :
    chkD4 d4Reps d4Words d4Wit [b1344Words, a85Words] = true := by
  have hs : d4Reps.size = 30 := rfl
  unfold chkD4
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, rfl⟩, wf_bool wf_idRows⟩, ?_⟩, ?_⟩
  · rw [hs]
    rfl
  · exact List.all_eq_true.2 fun k _ => wf_bool (etaE_enc k).1
  · rw [hs]
    exact List.all_eq_true.2 fun i hi => rep_of hR hL hH hwf (List.mem_range.1 hi)

end CertificateChecks.KernelJ4Q

end
