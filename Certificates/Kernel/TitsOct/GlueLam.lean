module

public import Certificates.Kernel.TitsOct.Glue
public import Certificates.Kernel.TitsOct.ChecksLam
public import CFSG.Certificates.Kernel.TitsOctLamSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOct

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TwoF4LieSound
  CFSG.KC.TitsOctSound CFSG.KC.TitsOctLamK CFSG.KC.TitsOctLamSound CFSG.KD.TitsOct
  CFSG.KD.TitsOctLam CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.H13.F45Ru

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem ncard_fin (P : ℕ → Prop) [DecidablePred P] :
    {c : Fin 1755 | P c.val}.ncard = ((Finset.range 1755).filter P).card := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun c _ => c.val) (fun c hc => ?_) (fun a b _ _ h => Fin.ext h)
    (fun n hn => ?_)
  · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hc ⊢
    exact ⟨c.2, hc⟩
  · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
    exact ⟨⟨n, hn.1⟩, hn.2, rfl⟩

theorem dist0 (c : Fin 1755) : octGraph.dist (Sum.inl 0) (Sum.inl c) = layAt LAY0 c := by
  have := (lay_at lay0).1.dist_eq (Sum.inl c)
  rw [ofCode_zero] at this
  exact this

theorem distL {b LAY PAR : ℕ} (h : layK lpD PL b 1024 LAY PAR = true) (c : Fin 1755) :
    octGraph.dist (ofCode b) (Sum.inl c) = layAt LAY c :=
  (lay_at h).1.dist_eq (Sum.inl c)

theorem ncard_nb (x : Vtx) : (octGraph.neighborSet x).ncard = degK (vCode x) := by
  have hnb := nbOK
  have ha := vCode_lt x
  have hlt : ∀ k < degK (vCode x), nbK lpD PL (vCode x) k < 4680 := fun k hk =>
    (adjK_iff.1 ((hnb.1 _ ha _).2 ⟨k, hk, rfl⟩)).1
  have hset : octGraph.neighborSet x = ↑((Finset.range (degK (vCode x))).image
      (fun j => (ofCode (nbK lpD PL (vCode x) j) : Vtx))) := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio]
    rw [adj_iff]
    constructor
    · intro hw
      obtain ⟨j, hj, e⟩ := (hnb.1 _ ha (vCode w)).1 hw
      exact ⟨j, hj, by rw [e, ofCode_vCode]⟩
    · rintro ⟨j, hj, rfl⟩
      rw [vCode_ofCode (hlt j hj)]
      exact (hnb.1 _ ha _).2 ⟨j, hj, rfl⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj e
  have hi' : i < degK (vCode x) := Finset.mem_range.1 hi
  have hj' : j < degK (vCode x) := Finset.mem_range.1 hj
  have e' : vCode (ofCode (nbK lpD PL (vCode x) i)) = vCode (ofCode (nbK lpD PL (vCode x) j)) :=
    congrArg vCode e
  rw [vCode_ofCode (hlt i hi'), vCode_ofCode (hlt j hj')] at e'
  exact hnb.2 _ ha i hi' j hj' e'

theorem deg : (∀ p : Fin 1755, (octGraph.neighborSet (Sum.inl p)).ncard = 5) ∧
    ∀ v : Fin 2925, (octGraph.neighborSet (Sum.inr v)).ncard = 3 := by
  refine ⟨fun p => ?_, fun v => ?_⟩
  · rw [ncard_nb, degK_eq]
    simp [vCode]
  · rw [ncard_nb, degK_eq]
    simp [vCode]

theorem cnt_eq {d n : ℕ} (h : Nat.beq (layCnt LAY0 d) n = true) :
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = d}.ncard = n := by
  have e : {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = d} =
      {p : Fin 1755 | layAt LAY0 p.val = d} := by
    ext p
    simp only [Set.mem_setOf_eq, dist0]
  rw [e]
  refine (ncard_fin (fun x => layAt LAY0 x = d)).trans ?_
  rw [← layCnt_eq, Nat.eq_of_beq_eq_true h]

theorem facts7340 : (∀ p : Fin 1755, (octGraph.neighborSet (Sum.inl p)).ncard = 5) ∧
    (∀ v : Fin 2925, (octGraph.neighborSet (Sum.inr v)).ncard = 3) ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 2}.ncard = 10 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 4}.ncard = 80 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 6}.ncard = 640 ∧
    {p : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl p) = 8}.ncard = 1024 :=
  ⟨deg.1, deg.2, cnt_eq cnt2, cnt_eq cnt4, cnt_eq cnt6, cnt_eq cnt8⟩

theorem dist_g (g : ↥TA) (u v : Vtx) : octGraph.dist (g • u) (g • v) = octGraph.dist u v :=
  GPath.dist_smul poly.connected g u v

theorem dist0_g {g : ↥TA} (hg : g • (Sum.inl 0 : Vtx) = Sum.inl 0) (c : Vtx) :
    octGraph.dist (Sum.inl 0) (g • c) = octGraph.dist (Sum.inl 0) c := by
  have := dist_g g (Sum.inl 0) c
  rwa [hg] at this

theorem inl_eq (g : ↥TA) (c : Fin 1755) : (Sum.inl c : Vtx) = g • Sum.inl ((g⁻¹).1 c) := by
  rw [← smul_inl, smul_inv_smul]

theorem lam_g {g : ↥TA} (hg : g • (Sum.inl 0 : Vtx) = Sum.inl 0) (u c : Vtx) :
    (octGraph.dist (Sum.inl 0) (g • c) = 8 ∧ 0 < octGraph.dist (g • u) (g • c) ∧
      octGraph.dist (g • u) (g • c) < 8) ↔
    (octGraph.dist (Sum.inl 0) c = 8 ∧ 0 < octGraph.dist u c ∧ octGraph.dist u c < 8) := by
  simp only [dist0_g hg, dist_g]

theorem th_g {g : ↥TA} (hg : g • (Sum.inl 0 : Vtx) = Sum.inl 0) (u c : Vtx) :
    (octGraph.dist (Sum.inl 0) (g • c) = 8 ∧ ¬ (0 < octGraph.dist (g • u) (g • c) ∧
      octGraph.dist (g • u) (g • c) < 8)) ↔
    (octGraph.dist (Sum.inl 0) c = 8 ∧ ¬ (0 < octGraph.dist u c ∧ octGraph.dist u c < 8)) := by
  simp only [dist0_g hg, dist_g]

theorem ncard_lam_g {g : ↥TA} (hg : g • (Sum.inl 0 : Vtx) = Sum.inl 0) (u : Vtx) :
    {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (g • u) (Sum.inl c) ∧ octGraph.dist (g • u) (Sum.inl c) < 8}.ncard =
      {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist u (Sum.inl c) ∧ octGraph.dist u (Sum.inl c) < 8}.ncard := by
  symm
  refine Set.ncard_congr (fun c _ => g.1 c) (fun c hc => ?_) (fun a b _ _ e => g.1.injective e)
    (fun c hc => ⟨(g⁻¹).1 c, ?_, ?_⟩)
  · simp only [Set.mem_setOf_eq] at hc ⊢
    rw [← smul_inl g c, lam_g hg]
    exact hc
  · simp only [Set.mem_setOf_eq] at hc ⊢
    rw [inl_eq g c, lam_g hg] at hc
    exact hc
  · have := inl_eq g c
    rw [smul_inl] at this
    exact (Sum.inl_injective this).symm

theorem q7_g {g : ↥TA} (hg : g • (Sum.inl 0 : Vtx) = Sum.inl 0) (y x : Vtx) :
    ({c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (g • y) (Sum.inl c) ∧ octGraph.dist (g • y) (Sum.inl c) < 8} =
      {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        ¬ (0 < octGraph.dist (g • x) (Sum.inl c) ∧ octGraph.dist (g • x) (Sum.inl c) < 8)}) ↔
    ({c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist y (Sum.inl c) ∧ octGraph.dist y (Sum.inl c) < 8} =
      {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        ¬ (0 < octGraph.dist x (Sum.inl c) ∧ octGraph.dist x (Sum.inl c) < 8)}) := by
  simp only [Set.ext_iff, Set.mem_setOf_eq]
  constructor
  · intro h c
    have := h (g.1 c)
    rw [← smul_inl g c, lam_g hg, th_g hg] at this
    exact this
  · intro h c
    rw [inl_eq g c, lam_g hg, th_g hg]
    exact h _

@[expose] noncomputable def aX (j : ℕ) : ↥TA := if j < 5 then wEl (fwPt.getD j []) else wEl wX

theorem codesX : CodesOK wX := by
  unfold CodesOK
  decide +kernel

theorem aX_ev {j : ℕ} (hj : j < 6) {y : ℕ} (hy : y < 1755) : gp (FX j) y = ev (aX j).1 y := by
  obtain ⟨hl5, -, hc1, -, -, -⟩ := dWords
  unfold FX aX
  rw [nIf_d, blt_d]
  by_cases h5 : j < 5
  · simp only [h5, decide_true, if_true]
    have hj' : j < fwPt.length := by rw [hl5]; exact h5
    rw [bindK_sound bindP j hj' y hy, getD_eq _ hj', wPt_ev (hc1 _ (List.getElem_mem hj')) hy]
  · simp only [h5, decide_false, Bool.false_eq_true, if_false]
    rw [bindK_sound bindX 0 (by simp) y hy]
    exact wPt_ev codesX hy

theorem aX_smul {j : ℕ} (hj : j < 6) {y : ℕ} (hy : y < 1755) :
    aX j • ofCode y = ofCode (gp (FX j) y) := by
  have hf : ∀ z < 1755, gp (FX j) z = ev (aX j).1 z := fun z hz => aX_ev hj hz
  have hx : gp (FX j) y < 1755 := by rw [hf y hy]; exact ev_lt _ hy
  exact (actV_iff hf (by omega) (by omega)).1 ((actV_pt hy).2 ⟨hx, rfl⟩)

theorem aX_fix {j : ℕ} (hj : j < 6) : aX j • (Sum.inl 0 : Vtx) = Sum.inl 0 := by
  have h0 : gp (FX j) 0 = 0 := by
    unfold FX
    rw [nIf_d, blt_d]
    by_cases h5 : j < 5
    · simp only [h5, decide_true, if_true]
      have := (fixV_sound (allN_iff'.1 fix0 j h5)).1
      rw [actV_pt (by norm_num)] at this
      exact this.2
    · simp only [h5, decide_false, Bool.false_eq_true, if_false]
      exact Nat.eq_of_beq_eq_true fixX
  have := aX_smul hj (y := 0) (by norm_num)
  rwa [h0, ofCode_zero] at this

theorem reach {root cnt l ORD PR LB PS : ℕ} (h : recPK FX 6 root cnt LAY0 l ORD PR LB PS = true)
    (x : Fin 1755) (hx : layAt LAY0 x = l) :
    ∃ g : ↥TA, g • (Sum.inl 0 : Vtx) = Sum.inl 0 ∧ g • ofCode root = Sum.inl x := by
  obtain ⟨g, hg, e⟩ := recP_reach (c := ofCode) (a := aX) (S := aX '' {j | j < 6})
    (fun j hj => ⟨j, hj, rfl⟩) (fun j hj y hy => aX_smul hj hy) h x x.2 hx
  have hle : Subgroup.closure (aX '' {j | j < 6}) ≤
      MulAction.stabilizer ↥TA (Sum.inl 0 : Vtx) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact MulAction.mem_stabilizer_iff.2 (aX_fix hj)
  refine ⟨g, MulAction.mem_stabilizer_iff.1 (hle hg), ?_⟩
  rw [e, ofCode_inl x.2]

theorem lam_root {b PAR LAYJ : ℕ} (hl : layK lpD PL b 1024 LAYJ PAR = true) :
    {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (ofCode b) (Sum.inl c) ∧ octGraph.dist (ofCode b) (Sum.inl c) < 8}.ncard =
      lamCnt LAY0 LAYJ := by
  have e : {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (ofCode b) (Sum.inl c) ∧ octGraph.dist (ofCode b) (Sum.inl c) < 8} =
      {c : Fin 1755 | layAt LAY0 c.val = 8 ∧ 0 < layAt LAYJ c.val ∧ layAt LAYJ c.val < 8} := by
    ext c
    simp only [Set.mem_setOf_eq, dist0, distL hl]
  rw [e, lamCnt_eq]
  exact ncard_fin (fun x => layAt LAY0 x = 8 ∧ 0 < layAt LAYJ x ∧ layAt LAYJ x < 8)

theorem lam_of {root cnt l ORD PR LB PS LAYJ PAR : ℕ}
    (hr : recPK FX 6 root cnt LAY0 l ORD PR LB PS = true)
    (hl : layK lpD PL root 1024 LAYJ PAR = true) (j : Fin 1755)
    (hj : octGraph.dist (Sum.inl 0) (Sum.inl j) = l) :
    {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl j) (Sum.inl c) ∧ octGraph.dist (Sum.inl j) (Sum.inl c) < 8}.ncard =
      lamCnt LAY0 LAYJ := by
  rw [dist0] at hj
  obtain ⟨g, hg0, hgr⟩ := reach hr j hj
  rw [← hgr, ncard_lam_g hg0]
  exact lam_root hl

theorem q12 (j : Fin 1755) (hj : octGraph.dist (Sum.inl 0) (Sum.inl j) = 2 ∨
      octGraph.dist (Sum.inl 0) (Sum.inl j) = 4 ∨ octGraph.dist (Sum.inl 0) (Sum.inl j) = 6) :
    {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl j) (Sum.inl c) ∧ octGraph.dist (Sum.inl j) (Sum.inl c) < 8}.ncard
      ≤ 2 ^ 9 ∧
    ({c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl j) (Sum.inl c) ∧ octGraph.dist (Sum.inl j) (Sum.inl c) < 8}.ncard
      = 2 ^ 9 ↔ octGraph.dist (Sum.inl 0) (Sum.inl j) = 2) := by
  rcases hj with h | h | h
  · rw [lam_of recA layA j h, Nat.eq_of_beq_eq_true lamA, h]
    norm_num
  · rw [lam_of recC layC j h, Nat.eq_of_beq_eq_true lamC, h]
    norm_num
  · rw [lam_of recD layD j h, Nat.eq_of_beq_eq_true lamD, h]
    norm_num

theorem pt012 (w : Vtx) (h0 : octGraph.Adj (Sum.inl 0) w) (h1 : octGraph.Adj (ofCode 1) w)
    (p : Fin 1755) (hp : octGraph.Adj (Sum.inl p) w) : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 := by
  have hnb := nbOK
  rw [adj_iff] at h0 h1 hp
  rw [vCode_ofCode (by norm_num)] at h1
  change adjK lpD 0 (vCode w) = true at h0
  change adjK lpD p (vCode w) = true at hp
  obtain ⟨k, hk, e⟩ := (hnb.1 0 (by norm_num) (vCode w)).1 h0
  rw [degK_eq, if_pos (by norm_num)] at hk
  rw [nbK_pt (by norm_num)] at e
  have hl := allN_iff'.1 line12 k hk
  rw [strictB_eq', bIf_d] at hl
  obtain ⟨-, -, ⟨-, -, h1'⟩ | ⟨h', -⟩⟩ := adjK_iff.1 h1
  · obtain ⟨-, -, ⟨-, -, hp'⟩ | ⟨h'', -⟩⟩ := adjK_iff.1 hp
    · have hv : vCode w - 1755 = plK PL 0 k := by omega
      rw [hv] at h1' hp'
      rw [if_pos h1', allN_iff'] at hl
      obtain ⟨m, hm, em⟩ := onLine_iff.1 hp'
      have := hl m hm
      simp only [strictB_eq', Nat.add_eq, Nat.mul_eq] at this
      rw [em, bIf_d, bIf_d] at this
      rcases Nat.lt_or_ge (p : ℕ) 3 with h3 | h3
      · omega
      · exfalso
        simp [beq_d, show (p : ℕ) ≠ 0 by omega, show (p : ℕ) ≠ 1 by omega,
          show (p : ℕ) ≠ 2 by omega] at this
    · have := p.2
      omega
  · omega

theorem setB :
    {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (ofCode 2) (Sum.inl c) ∧ octGraph.dist (ofCode 2) (Sum.inl c) < 8} =
      {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        ¬ (0 < octGraph.dist (ofCode 1) (Sum.inl c) ∧ octGraph.dist (ofCode 1) (Sum.inl c) < 8)} := by
  ext c
  simp only [Set.mem_setOf_eq, dist0, distL layA, distL layB]
  have := cmpK_sound cmpAB c c.2
  simp only [Bool.eq_false_iff, ne_eq, midL_iff] at this
  exact ⟨fun ⟨h8, hb⟩ => ⟨h8, (this h8).1 hb⟩, fun ⟨h8, ha⟩ => ⟨h8, (this h8).2 ha⟩⟩

theorem walk_dist {P : List ℕ} (h : walkK lpD LAY0 LAYA P = true) :
    octGraph.dist (ofCode (P.headD 0)) (ofCode (P.getLastD 0)) ≤ 7 := by
  obtain ⟨hpos, hlen, hadj, -, -, -⟩ := walkK_sound h
  have key : ∀ i, i < P.length →
      ∃ w : octGraph.Walk (ofCode (P.getD 0 0)) (ofCode (P.getD i 0)), w.length = i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨SimpleGraph.Walk.nil, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨w, hw⟩ := ih (by omega)
      have ha := hadj i hi
      have h' : octGraph.Adj (ofCode (P.getD i 0)) (ofCode (P.getD (i + 1) 0)) := by
        obtain ⟨l1, l2, -⟩ := adjK_iff.1 ha
        rw [adj_iff, vCode_ofCode l2, vCode_ofCode l1]
        exact ha
      exact ⟨w.concat h', by simp [hw]⟩
  obtain ⟨w, hw⟩ := key (P.length - 1) (by omega)
  have e1 : P.headD 0 = P.getD 0 0 := by cases P <;> simp
  have e2 : P.getLastD 0 = P.getD (P.length - 1) 0 := by
    simp [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  rw [e1, e2]
  calc _ ≤ w.length := SimpleGraph.dist_le w
    _ ≤ 7 := by omega

theorem q7_one (y : Fin 1755) (hy : octGraph.dist (Sum.inl 0) (Sum.inl y) = 2) :
    {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl y) (Sum.inl c) ∧ octGraph.dist (Sum.inl y) (Sum.inl c) < 8} =
      {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        ¬ (0 < octGraph.dist (ofCode 1) (Sum.inl c) ∧ octGraph.dist (ofCode 1) (Sum.inl c) < 8)} ↔
      y.val = 2 := by
  constructor
  · intro hset
    by_contra hne
    rw [dist0] at hy
    obtain ⟨P, hP, hh⟩ := starts_sound startW y y.2 hy hne
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hP
    have hwk : walkK lpD LAY0 LAYA W[k] = true := (allL_iff W 0).1 walks k hk
    obtain ⟨-, -, -, hc, h8, hm⟩ := walkK_sound hwk
    have hd := walk_dist hwk
    rw [hh] at hd
    simp only [ofCode_inl y.2, ofCode_inl hc, Fin.eta] at hd
    have hne' : (Sum.inl y : Vtx) ≠ Sum.inl ⟨W[k].getLastD 0, hc⟩ := by
      intro e
      have e' := congrArg (fun v : Vtx => layAt LAY0 (vCode v)) e
      simp only [vCode] at e'
      omega
    have hmem : (⟨W[k].getLastD 0, hc⟩ : Fin 1755) ∈ {c : Fin 1755 |
        octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧ 0 < octGraph.dist (Sum.inl y) (Sum.inl c) ∧
          octGraph.dist (Sum.inl y) (Sum.inl c) < 8} := by
      rw [Set.mem_setOf_eq, dist0]
      exact ⟨h8, (poly.connected.preconnected _ _).pos_dist_of_ne hne', by omega⟩
    rw [hset, Set.mem_setOf_eq, distL layA] at hmem
    exact hmem.2 (midL_iff.1 hm)
  · intro h2
    have e : (ofCode 2 : Vtx) = Sum.inl y := by
      rw [ofCode_inl (by norm_num)]
      exact congrArg Sum.inl (Fin.ext h2.symm)
    rw [← e]
    exact setB

theorem q7 (x y x' : Fin 1755) (l : Fin 2925)
    (hx : octGraph.dist (Sum.inl 0) (Sum.inl x) = 2)
    (hy : octGraph.dist (Sum.inl 0) (Sum.inl y) = 2)
    (h0 : octGraph.Adj (Sum.inl 0) (Sum.inr l)) (hxl : octGraph.Adj (Sum.inl x) (Sum.inr l))
    (hx'l : octGraph.Adj (Sum.inl x') (Sum.inr l)) (hx'0 : x' ≠ 0) (hx'x : x' ≠ x) :
    ({c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        0 < octGraph.dist (Sum.inl y) (Sum.inl c) ∧ octGraph.dist (Sum.inl y) (Sum.inl c) < 8} =
      {c : Fin 1755 | octGraph.dist (Sum.inl 0) (Sum.inl c) = 8 ∧
        ¬ (0 < octGraph.dist (Sum.inl x) (Sum.inl c) ∧ octGraph.dist (Sum.inl x) (Sum.inl c) < 8)} ↔
      y = x') := by
  rw [dist0] at hx
  obtain ⟨g, hg0, hg1⟩ := reach recA x hx
  obtain ⟨x₁, hx₁g⟩ : ∃ x₁ : Fin 1755, g • (Sum.inl x₁ : Vtx) = Sum.inl x' :=
    ⟨(g⁻¹).1 x', by rw [← smul_inl, smul_inv_smul]⟩
  obtain ⟨y₁, hy₁g⟩ : ∃ y₁ : Fin 1755, g • (Sum.inl y₁ : Vtx) = Sum.inl y :=
    ⟨(g⁻¹).1 y, by rw [← smul_inl, smul_inv_smul]⟩
  have hw : g • (g⁻¹ • (Sum.inr l : Vtx)) = Sum.inr l := smul_inv_smul g _
  rw [← hg0, ← hw] at h0
  rw [← hg1, ← hw] at hxl
  rw [← hx₁g, ← hw] at hx'l
  have hp := pt012 _ ((GraphAction.adj_smul g _ _).1 h0) ((GraphAction.adj_smul g _ _).1 hxl) x₁
    ((GraphAction.adj_smul g _ _).1 hx'l)
  have hne0 : x₁.val ≠ 0 := fun h => hx'0 (by
    have e : x₁ = 0 := Fin.ext h
    rw [e, hg0] at hx₁g
    exact (Sum.inl_injective hx₁g).symm)
  have hne1 : x₁.val ≠ 1 := fun h => hx'x (by
    have e : (Sum.inl x₁ : Vtx) = ofCode 1 := by
      rw [ofCode_inl (by norm_num)]
      exact congrArg Sum.inl (Fin.ext h)
    rw [e, hg1] at hx₁g
    exact (Sum.inl_injective hx₁g).symm)
  have h2 : x₁.val = 2 := by omega
  have hy₁ : octGraph.dist (Sum.inl 0) (Sum.inl y₁) = 2 := by
    have := dist_g g (Sum.inl 0) (Sum.inl y₁)
    rw [hg0, hy₁g, hy] at this
    exact this.symm
  rw [← hy₁g, ← hg1, q7_g hg0, q7_one y₁ hy₁]
  constructor
  · intro h
    have e : y₁ = x₁ := Fin.ext (by rw [h, h2])
    exact Sum.inl_injective (by rw [← hy₁g, ← hx₁g, e])
  · intro h
    have e : (Sum.inl y₁ : Vtx) = Sum.inl x₁ := smul_left_cancel g (by rw [hy₁g, hx₁g, h])
    rw [Sum.inl_injective e]
    exact h2

end CertificateChecks.KernelTitsOct

end
