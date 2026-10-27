module

public import CFSG.Sporadic.J4.QT2ANative
public import Certificates.Kernel.J4Q.QT2AC
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A

theorem nocomm_eq {X Y : Array V2} {x y : Nat} (hX : WfA X ∧ encR X = x) (hY : WfA Y ∧ encR Y = y) :
    nocomm X Y = !Nat.beq (mulJ c rm x y) (mulJ c rm y x) := by
  rw [nocomm, eqRows_of (mul_enc hK hX hY) (mul_enc hK hY hX)]

theorem mod_ok : chkMod = true := by
  unfold chkMod
  rw [eqRows_of (mul_enc hK bInv_enc bRows_enc) (id_enc hK),
    eqRows_of (mul_enc hK bRows_enc (mul_enc hK phiR_enc qt2a_pRows_enc)) patRows_enc,
    eqRows_of (mul_enc hK qt2a_pRows_enc qt2a_pInv_enc) (id_enc hK),
    eqRows_of (mul_enc hK zR_enc zR_enc) (id_enc hK), ← Array.all_toList]
  quickRfl

theorem tab_chk : allR 27 (fun n =>
    andB (andB (Nat.blt (getN 0 TA n) 27)
        (Nat.beq (mulJ c rm (getN one YEs n) YA) (getN one YEs (getN 0 TA n))))
      (andB (Nat.blt (getN 0 TB n) 27)
        (Nat.beq (mulJ c rm (getN one YEs n) YB) (getN one YEs (getN 0 TB n))))) = true := by
  quickRfl

theorem y_ok : chkY = true := by
  unfold chkY
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, wf_bool ya_enc.1⟩, wf_bool yb_enc.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [cmz_eq' ya_enc]
    quickRfl
  · rw [cmz_eq' yb_enc]
    quickRfl
  · rw [eqRows_of (yEl_enc (n := 0) (by decide)) (id_enc hK)]
    quickRfl
  · exact List.all_eq_true.2 fun n hn => wf_bool (yEl_enc (List.mem_range.1 hn)).1
  · rw [allDistinct_enc _ (fun X hX => by
        obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hX
        exact (yEl_enc (List.mem_range.1 hn)).1), List.map_map,
      List.map_congr_left (f := encR ∘ yEl) (g := getN one YEs) (fun n hn => (yEl_enc (List.mem_range.1 hn)).2)]
    quickRfl
  · refine List.all_eq_true.2 fun n hn => ?_
    have hn' := List.mem_range.1 hn
    have h := allR_spec tab_chk n hn'
    simp only [andB_eq, Bool.and_eq_true] at h
    obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := h
    have ia := lt_of_blt ha1
    have ib := lt_of_blt hb1
    rw [Bool.and_eq_true]
    refine ⟨List.any_eq_true.2 ⟨getN 0 TA n, List.mem_range.2 ia, ?_⟩,
      List.any_eq_true.2 ⟨getN 0 TB n, List.mem_range.2 ib, ?_⟩⟩
    · rw [eqRows_of (mul_enc hK (yEl_enc hn') ya_enc) (yEl_enc ia)]
      exact ha2
    · rw [eqRows_of (mul_enc hK (yEl_enc hn') yb_enc) (yEl_enc ib)]
      exact hb2

theorem yr_of {R : Array V2} {x : Nat} (h : WfA R ∧ encR R = x) (r : Nat)
    (hk : (Nat.beq (mulJ c rm x ZM) (mulJ c rm ZM x) && Nat.beq (powJ c rm one x r) one &&
      !Nat.beq x one) = true) : chkYr R r = true := by
  have hw : wfR R = true := wf_bool h.1
  unfold chkYr
  rw [cmz_eq' h, eqRows_of (pow_enc hK h r) (id_enc hK), eqRows_of h (id_enc hK), hw, Bool.and_true]
  exact hk

theorem qgens_ok : chkQgens = true := by
  unfold chkQgens
  rw [qGenW_eq, all_range_congr (f := fun k => inQz (qR k))
    (g := fun k => Nat.beq (mulJ c rm (getN one QAs k) ZM) (mulJ c rm ZM (getN one QAs k)) &&
      trivK rm PM CVs (getN one QAs k))
    (fun k hk => by rw [inQz, cmz_eq' (qR_enc hk), triv_eq (qR_enc hk)])]
  quickRfl

theorem notQzY_ok : chkNotQzY = true := by
  unfold chkNotQzY
  rw [all_range_congr (f := fun n => n == 0 || notQz (yEl n))
    (g := fun n => n == 0 || !trivK rm PM CVs (getN one YEs n))
    (fun n hn => by rw [notQz, triv_eq (yEl_enc hn)])]
  quickRfl

theorem notQzPow_of {R : Array V2} {x : Nat} (h : WfA R ∧ encR R = x) (r : Nat)
    (hk : (List.range (r - 1)).all (fun k => !trivK rm PM CVs (powJ c rm one x (k + 1))) = true) :
    chkNotQzPow R r = true := by
  unfold chkNotQzPow
  rw [all_range_congr (f := fun k => notQz (powRows R (k + 1)))
    (g := fun k => !trivK rm PM CVs (powJ c rm one x (k + 1)))
    (fun k _ => by rw [notQz, triv_eq (pow_enc hK h (k + 1))])]
  exact hk

theorem wit_ok : chkWit = true := by
  have q0 := qR_enc (k := 0) (by decide)
  unfold chkWit
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨wf_bool q0.1, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [all_range_congr (f := fun n => n == 0 || nocomm (qR 0) (yEl n))
      (g := fun n => n == 0 || !Nat.beq (mulJ c rm (getN one QAs 0) (getN one YEs n))
        (mulJ c rm (getN one YEs n) (getN one QAs 0)))
      (fun n hn => by rw [nocomm_eq q0 (yEl_enc hn)])]
    quickRfl
  · rw [all_range_congr (f := fun k => nocomm (qR 0) (powRows (y5R ()) (k + 1)))
      (g := fun k => !Nat.beq (mulJ c rm (getN one QAs 0) (powJ c rm one YP5 (k + 1)))
        (mulJ c rm (powJ c rm one YP5 (k + 1)) (getN one QAs 0)))
      (fun k _ => by rw [nocomm_eq q0 (pow_enc hK y5_enc (k + 1))])]
    quickRfl
  · rw [all_range_congr (f := fun k => nocomm (qR 0) (powRows (y7R ()) (k + 1)))
      (g := fun k => !Nat.beq (mulJ c rm (getN one QAs 0) (powJ c rm one YP7 (k + 1)))
        (mulJ c rm (powJ c rm one YP7 (k + 1)) (getN one QAs 0)))
      (fun k _ => by rw [nocomm_eq q0 (pow_enc hK y7_enc (k + 1))])]
    quickRfl
  · rw [all_range_congr (f := fun k => nocomm (qR 0) (powRows (y11R ()) (k + 1)))
      (g := fun k => !Nat.beq (mulJ c rm (getN one QAs 0) (powJ c rm one YP11 (k + 1)))
        (mulJ c rm (powJ c rm one YP11 (k + 1)) (getN one QAs 0)))
      (fun k _ => by rw [nocomm_eq q0 (pow_enc hK y11_enc (k + 1))])]
    quickRfl

@[expose] noncomputable def eK (n : Nat) : Bool :=
  orB (Nat.beq n 0) (andB (Nat.beq (eMasks.getD n []).length 6)
    (strictB (getN one YEs n) fun y => distinctK (smapK (fun t =>
      strictN (etaK c rm one Us (combMask (eMasks.getD n []) t)) fun e => mulJ c rm (mulJ c rm e y) e)
      (rangeK 64))))

#j4q_all CFSG.KD.J4Q.EC CertificateChecks.KernelJ4Q.eK 27

theorem eConj_of {n : Nat} (hn : n < 27)
    (h : andB (Nat.beq (eMasks.getD n []).length 6)
      (strictB (getN one YEs n) fun y => distinctK (smapK (fun t =>
        strictN (etaK c rm one Us (combMask (eMasks.getD n []) t)) fun e => mulJ c rm (mulJ c rm e y) e)
        (rangeK 64))) = true) :
    eConjOK n = true := by
  rw [andB_eq, Bool.and_eq_true, strictB_eq, smapK_eq, rangeK_eq] at h
  have hc : ∀ t, WfA (conjE (combMask (eMasks.getD n []) t) (yEl n)) ∧
      encR (conjE (combMask (eMasks.getD n []) t) (yEl n)) =
        strictN (etaK c rm one Us (combMask (eMasks.getD n []) t))
          fun e => mulJ c rm (mulJ c rm e (getN one YEs n)) e := by
    intro t
    rw [strictN_eq]
    exact mul_enc hK (mul_enc hK (eta_enc _) (yEl_enc hn)) (eta_enc _)
  have hwf : ∀ X ∈ (List.range 64).map (fun t => conjE (combMask (eMasks.getD n []) t) (yEl n)),
      WfA X := by
    intro X hX
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hX
    exact (hc t).1
  unfold eConjOK
  simp only []
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨beq_iff_eq.2 (Nat.eq_of_beq_eq_true h.1), List.all_eq_true.2 fun X hX => wf_bool (hwf X hX)⟩,
    ?_⟩
  rw [allDistinct_enc _ hwf, List.map_map]
  have : (encR ∘ fun t => conjE (combMask (eMasks.getD n []) t) (yEl n)) =
      fun t => strictN (etaK c rm one Us (combMask (eMasks.getD n []) t))
        fun e => mulJ c rm (mulJ c rm e (getN one YEs n)) e := by
    funext t
    exact (hc t).2
  rw [this]
  exact h.2

theorem e_ok : chkE = true := by
  unfold chkE
  refine List.all_eq_true.2 fun n hn => ?_
  have hn' := List.mem_range.1 hn
  have h := EC.all n hn'
  by_cases h0 : n = 0
  · subst h0
    rfl
  · rw [eK, nbeq_false h0] at h
    rw [eConj_of hn' h, Bool.or_true]

theorem qSub_lt : ∀ j < 6, qSub.getD j 0 < 12 := by decide

@[expose] noncomputable def PQ : List (Nat × Nat) :=
  (List.range 6).map fun j => (j, getN one QAs (qSub.getD j 0))

@[expose] noncomputable def PQi : List (Nat × Nat) :=
  (List.range 6).reverse.map fun j => (j, getN one QIs (qSub.getD j 0))

theorem qWord_enc (t : Nat) : encR (wR (qWordG qSub t)) = selPK c rm PQ t one := by
  have hP : PQ.map Prod.fst = List.range 6 := by
    rw [PQ, List.map_map]
    exact List.map_id _
  have := enc_selRows hK (fun j => wR (qGenW.getD (qSub.getD j 0) [])) t PQ (by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact qR_enc (qSub_lt j (List.mem_range.1 hj))) (idRows ()) wf_idRows
  rw [hP, enc_idRows hK] at this
  rw [wR_qWordG]
  exact this.2

theorem qWordi_enc (t : Nat) : encR (wR (invW (qWordG qSub t))) = selPK c rm PQi t one := by
  have hP : PQi.map Prod.fst = (List.range 6).reverse := by
    rw [PQi, List.map_map]
    exact List.map_id _
  have := enc_selRows hK (fun j => wR (invW (qGenW.getD (qSub.getD j 0) []))) t PQi (by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact qRi_enc (qSub_lt j (List.mem_range.1 (List.mem_reverse.1 hj)))) (idRows ()) wf_idRows
  rw [hP, enc_idRows hK] at this
  rw [wR_invW_qWordG]
  exact this.2

@[expose] noncomputable def qcK (n : Nat) : Bool :=
  orB (Nat.beq n 0) (strictB (getN one YEs n) fun x => distinctK (smapK (fun t =>
    mulJ c rm (mulJ c rm (selPK c rm PQ t one) x) (selPK c rm PQi t one)) (rangeK 64)))

#j4q_all CFSG.KD.J4Q.QC CertificateChecks.KernelJ4Q.qcK 27

theorem qconj_ok : chkQconj = true := by
  have hn : ∀ n < 27, (n == 0 || conjDistinct (qWordG qSub) (yEl n)) = true := by
    intro n hn
    have h := QC.all n hn
    by_cases h0 : n = 0
    · subst h0
      rfl
    · rw [qcK, nbeq_false h0] at h
      rw [conjDistinct_of _ _ _ qWord_enc qWordi_enc _ _ (yEl_enc hn).1 (yEl_enc hn).2 h,
        Bool.or_true]
  have hps : ((List.range 64).map fun t => wR (qWordG qSub t)).all wfR = true :=
    List.all_eq_true.2 fun X hX => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hX
      exact wf_bool (wR_enc _).1
  unfold chkQconj
  simp only []
  rw [Bool.and_eq_true]
  exact ⟨hps, List.all_eq_true.2 fun n hn' => hn n (List.mem_range.1 hn')⟩

theorem chkLoc_ok : chkLoc = true := by
  unfold chkLoc
  rw [aDw_eq, bDw_eq]
  quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2A in
theorem c4000 : (chkMod = true)
    ∧ (chkY = true)
    ∧ (chkYr (y5R ()) 5 = true)
    ∧ (chkYr (y7R ()) 7 = true)
    ∧ (chkYr (y11R ()) 11 = true)
    ∧ (chkQgens = true)
    ∧ (chkNotQzY = true)
    ∧ (chkNotQzPow (y5R ()) 5 = true)
    ∧ (chkNotQzPow (y7R ()) 7 = true)
    ∧ (chkNotQzPow (y11R ()) 11 = true)
    ∧ (chkWit = true)
    ∧ (chkE = true)
    ∧ (chkQconj = true)
    ∧ (chkLoc = true) :=
  ⟨mod_ok, y_ok, yr_of y5_enc 5 (by quickRfl), yr_of y7_enc 7 (by quickRfl),
    yr_of y11_enc 11 (by quickRfl), qgens_ok, notQzY_ok, notQzPow_of y5_enc 5 (by quickRfl),
    notQzPow_of y7_enc 7 (by quickRfl), notQzPow_of y11_enc 11 (by quickRfl), wit_ok, e_ok,
    qconj_ok, chkLoc_ok⟩

end CertificateChecks.KernelJ4Q

end
