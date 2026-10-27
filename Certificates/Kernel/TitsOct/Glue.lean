
module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLocal
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLayers
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuPoly
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public import Certificates.Kernel.TitsOct.Checks
public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Certificates.Kernel.TitsOctSound
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOct

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TwoF4LieSound
  CFSG.KC.TitsOctSound CFSG.KD.TitsOct CFSG.Sporadic.Schreier.Tits CFSG.Quasithin
  CFSG.Quasithin.H13.F45Ru
open CertificateChecks.KernelSporSch.TitsAction (lpK k4)

open scoped Pointwise

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem lpD_eq {i : ℕ} (hi : i < 8775) : lpD i = lpK i := by
  have h := lpEq
  rw [bAnd_eq', Bool.and_eq_true, allN_iff'] at h
  exact Nat.eq_of_beq_eq_true (h.2 i hi)

theorem k4' {v : ℕ} (hv : v < 2925) :
    lpK (3 * v) < lpK (3 * v + 1) ∧ lpK (3 * v + 1) < lpK (3 * v + 2) ∧ lpK (3 * v + 2) < 1755 := by
  have h := allN_iff'.1 k4 v hv
  simp only [bAnd_eq', Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem hlp {i : ℕ} (hi : i < 8775) : lpD i < 1755 := by
  rw [lpD_eq hi]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ i = 3 * q + r :=
    ⟨i / 3, i % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 3).symm⟩
  have := k4' (v := q) (by omega)
  interval_cases r
  · simp only [Nat.add_zero]
    omega
  · omega
  · omega

theorem hlpd {v : ℕ} (hv : v < 2925) {k : ℕ} (hk : k < 3) {j : ℕ} (hj : j < 3)
    (e : lpD (3 * v + k) = lpD (3 * v + j)) : k = j := by
  rw [lpD_eq (by omega), lpD_eq (by omega)] at e
  have := k4' hv
  interval_cases k <;> interval_cases j <;> (try simp only [Nat.add_zero] at e) <;> omega

theorem nbOK : NbOK lpD PL :=
  nbOK_of_incK (fun _ hi => hlp hi) (fun _ hv _ hk _ hj e => hlpd hv hk hj e) inc

theorem lpK_pt (v : Fin 2925) {k : ℕ} (hk : k < 3) : lpK (3 * v + k) = titsLinePt v k := by
  rw [titsLinePt_val v hk, CertificateChecks.KernelSporSch.TitsAction.lp_get (by omega)]

theorem lineK (v : Fin 2925) (p : Fin 1755) : p ∈ titsLine v ↔ ∃ k < 3, lpK (3 * v + k) = p := by
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := RuType.J47.exists_linePt_of_mem h
    exact ⟨k, hk, by rw [lpK_pt v hk, e]⟩
  · rintro ⟨k, hk, e⟩
    have e' : titsLinePt v k = p := Fin.ext (by rw [← lpK_pt v hk, e])
    rw [← e']
    exact RuType.J47.linePt_mem v hk

theorem onLine_mem (p : Fin 1755) (v : Fin 2925) : onLine lpD p v = true ↔ p ∈ titsLine v := by
  have hv := v.2
  rw [onLine_iff, lineK]
  constructor
  · rintro ⟨k, hk, e⟩
    exact ⟨k, hk, by rw [← lpD_eq (by omega)]; exact e⟩
  · rintro ⟨k, hk, e⟩
    exact ⟨k, hk, by rw [lpD_eq (by omega)]; exact e⟩

theorem adj_iff (x y : Vtx) : octGraph.Adj x y ↔ adjK lpD (vCode x) (vCode y) = true := by
  rw [adjK_iff]
  cases x with
  | inl p =>
    have hp := p.2
    cases y with
    | inl q =>
      have hq := q.2
      refine ⟨fun h => (h : False).elim, ?_⟩
      simp only [vCode]
      rintro ⟨-, -, ⟨-, h, -⟩ | ⟨h, -⟩⟩ <;> omega
    | inr v =>
      have hv := v.2
      rw [octGraph_adj_inl_inr, ← onLine_mem]
      simp only [vCode, Nat.add_sub_cancel_left]
      constructor
      · intro h
        exact ⟨by omega, by omega, Or.inl ⟨hp, by omega, h⟩⟩
      · rintro ⟨-, -, ⟨-, -, h⟩ | ⟨h, -⟩⟩
        · exact h
        · omega
  | inr v =>
    have hv := v.2
    cases y with
    | inl p =>
      have hp := p.2
      rw [octGraph_adj_inr_inl, ← onLine_mem]
      simp only [vCode, Nat.add_sub_cancel_left]
      constructor
      · intro h
        exact ⟨by omega, by omega, Or.inr ⟨by omega, hp, h⟩⟩
      · rintro ⟨-, -, ⟨h, -⟩ | ⟨-, -, h⟩⟩
        · omega
        · exact h
    | inr w =>
      have hw := w.2
      refine ⟨fun h => (h : False).elim, ?_⟩
      simp only [vCode]
      rintro ⟨-, -, ⟨h, -⟩ | ⟨-, h, -⟩⟩ <;> omega

theorem lay_at {b cnt LAY PAR : ℕ} (h : layK lpD PL b cnt LAY PAR = true) :
    Layers octGraph 8 (ofCode b) (fun x => layAt LAY (vCode x)) ∧
      {y | octGraph.dist (ofCode b) y = 8}.ncard = cnt :=
  layers_of_layK vCode_lt ofCode_vCode (fun _ hn => vCode_ofCode hn) adj_iff nbOK h

theorem lpD_pt (v : Fin 2925) {k : ℕ} (hk : k < 3) : lpD (3 * v + k) = titsLinePt v k := by
  have := v.2
  rw [lpD_eq (by omega), lpK_pt v hk]

theorem line_iff {g : ↥TA} {f : ℕ → ℕ} (hf : ∀ y < 1755, f y = ev g.1 y) (v w : Fin 2925) :
    (∀ k < 3, onLine lpD (f (lpD (3 * v + k))) w = true) ↔ g.1 • titsLine v = titsLine w := by
  have key : ∀ k < 3, onLine lpD (f (lpD (3 * v + k))) w = true ↔
      g.1 (titsLinePt v k) ∈ titsLine w := by
    intro k hk
    rw [lpD_pt v hk, hf _ (titsLinePt v k).2, ev_fin, onLine_mem]
  constructor
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Finset.mem_smul_finset] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨k, hk, rfl⟩ := RuType.J47.exists_linePt_of_mem hx
      exact (key k hk).1 (h k hk)
    · rw [Finset.card_smul_finset, RuType.J47.card_titsLine, RuType.J47.card_titsLine]
  · intro h k hk
    rw [key k hk, ← h]
    exact Finset.smul_mem_smul_finset (RuType.J47.linePt_mem v hk)

theorem actV_iff {g : ↥TA} {f : ℕ → ℕ} (hf : ∀ y < 1755, f y = ev g.1 y) {y x : ℕ}
    (hy : y < 4680) (hx : x < 4680) : actV lpD f y x = true ↔ g • ofCode y = ofCode x := by
  by_cases hy1 : y < 1755
  · rw [actV_pt hy1, ofCode_inl hy1, smul_inl, hf y hy1]
    by_cases hx1 : x < 1755
    · rw [ofCode_inl hx1, Sum.inl.injEq, Fin.ext_iff]
      simp [ev, hy1, hx1]
    · rw [ofCode_inr (by omega) hx]
      simp [hx1]
  · have hy2 : 1755 ≤ y := by omega
    rw [actV_ln hy2, ofCode_inr hy2 hy, smul_inr]
    by_cases hx1 : x < 1755
    · rw [ofCode_inl hx1]
      simp [show ¬ 1755 ≤ x by omega]
    · rw [ofCode_inr (by omega) hx, Sum.inr.injEq, lineHom_eq_iff]
      have := line_iff hf ⟨y - 1755, by omega⟩ ⟨x - 1755, by omega⟩
      simp only at this
      rw [← this]
      simp only [show 1755 ≤ x by omega, hx, true_and]

theorem hF' : ∀ h < 4, PR (F h) (titsGen h) := fun h hh => CFSG.KS.Raw.Orb.prep_of_rep (by
  have := titsGen_rep hh
  rw [CertificateChecks.KernelSpor.Tits2264.gen_eq hh] at this
  exact this)

theorem codesMem {wd : List ℕ} (hw : CodesOK wd) : wordP titsGen wd ∈ TA := by
  unfold wordP
  refine Subgroup.list_prod_mem (K := TA) ?_
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  have h4 : c / 2 - 1 < 4 := by have := hw c hc; omega
  unfold letP
  split_ifs
  · exact titsGen_mem_titsA h4
  · exact Subgroup.inv_mem _ (titsGen_mem_titsA h4)

theorem hGI : ∀ h < 4, PR (GI h) (titsGen h)⁻¹ := fun h hh => by
  obtain ⟨g, hg, hgi⟩ := CFSG.KC.EnumSound.permOK_perm (allN_iff'.1 invG h hh)
  rwa [CFSG.KC.EnumSound.prep_unique hg (hF' h hh)] at hgi

open Classical in
@[expose] noncomputable def wEl (w : List ℕ) : ↥TA :=
  if h : CodesOK w then ⟨wordP titsGen w, codesMem h⟩ else 1

theorem wEl_val {w : List ℕ} (h : CodesOK w) : (wEl w).1 = wordP titsGen w := by
  simp [wEl, h]

theorem wPt_ev {w : List ℕ} (h : CodesOK w) {x : ℕ} (hx : x < 1755) :
    wPt F GI w x = ev (wEl w).1 x := by
  rw [wEl_val h, wPt_eq hF' hGI w h ⟨x, hx⟩]
  simp [ev, hx]

theorem wEl_nil : wEl [] = 1 := by
  apply Subtype.ext
  rw [wEl_val (fun c hc => by simp at hc)]
  simp [wordP]

theorem dWords : fwPt.length = 5 ∧ fwLn.length = 3 ∧ (∀ w ∈ fwPt, ∀ c ∈ w, 2 ≤ c ∧ c < 10) ∧
    (∀ w ∈ fwLn, ∀ c ∈ w, 2 ≤ c ∧ c < 10) ∧ (∀ w ∈ lwPt, ∀ c ∈ w, 2 ≤ c ∧ c < 10) ∧
    (∀ w ∈ lwLn, ∀ c ∈ w, 2 ≤ c ∧ c < 10) := by
  decide +kernel

theorem lay1862 : layAt LAY1 1862 = 8 := by decide +kernel

theorem getD_eq {α : Type*} {l : List α} {i : ℕ} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem localData_at {a b0 d k cnt nG LAY PAR ORD PA LB PS : ℕ} {A : ℕ → ℕ}
    {fw lw : List (List ℕ)} {prs : List ℕ}
    (ha : a < 4680) (hb0 : b0 < 4680) (hk : fw.length = k)
    (hcF : ∀ w ∈ fw, CodesOK w) (hcL : ∀ w ∈ lw, CodesOK w)
    (hbind : bindK F GI A fw = true)
    (hfix : allN k (fun j => fixV lpD PL (gp (A j)) a) = true)
    (hrec : recK lpD A k b0 cnt LAY ORD PA LB PS = true)
    (hlay : layK lpD PL a cnt LAY PAR = true) (hb8 : layAt LAY b0 = 8)
    (hloc : locK lpD F GI PL a b0 d lw prs = true) (hdeg : degK a = d)
    (hnG : Nat.card (MulAction.stabilizer ↥TA (ofCode a)) = nG)
    (hcard : d * (d - 1) * cnt = nG) (hpow : ∃ k, nG = 2 ^ k * d) (hodd : ¬ 2 ∣ d)
    (hd2 : 2 ≤ d) :
    ∃ (b₀ w₀ w₁ : Vtx) (Fg : Set ↥TA) (L : Finset ↥TA),
      LocalData ↥TA octGraph 8 (ofCode a) b₀ w₀ w₁ Fg L nG cnt d := by
  obtain ⟨hL, hcnt⟩ := lay_at hlay
  have hnb := nbOK
  have hofinj : ∀ n m, n < 4680 → m < 4680 → (ofCode n : Vtx) = ofCode m → n = m :=
    fun n m hn hm e => by rw [← vCode_ofCode hn, e, vCode_ofCode hm]
  have hnbr : ∀ j < d, nbK lpD PL a j < 4680 ∧ octGraph.Adj (ofCode a) (ofCode (nbK lpD PL a j)) := by
    intro j hj
    have h1 := (hnb.1 a ha (nbK lpD PL a j)).2 ⟨j, hdeg ▸ hj, rfl⟩
    have hlt := (adjK_iff.1 h1).1
    refine ⟨hlt, ?_⟩
    rw [adj_iff, vCode_ofCode ha, vCode_ofCode hlt]
    exact h1
  have hadjA : ∀ w, octGraph.Adj (ofCode a) w → ∃ j < d, ofCode (nbK lpD PL a j) = w := by
    intro w hw
    rw [adj_iff, vCode_ofCode ha] at hw
    obtain ⟨j, hj, e⟩ := (hnb.1 a ha (vCode w)).1 hw
    exact ⟨j, hdeg ▸ hj, by rw [e, ofCode_vCode]⟩
  have hnbi : ∀ i < d, ∀ j < d, (ofCode (nbK lpD PL a i) : Vtx) = ofCode (nbK lpD PL a j) → i = j :=
    fun i hi j hj e => hnb.2 a ha i (hdeg ▸ hi) j (hdeg ▸ hj)
      (hofinj _ _ (hnbr i hi).1 (hnbr j hj).1 e)
  have hAj : ∀ j < k, ∀ y < 1755, gp (A j) y = ev (wEl (fw.getD j [])).1 y := by
    intro j hj y hy
    have hj' : j < fw.length := hk ▸ hj
    rw [bindK_sound hbind j hj' y hy, getD_eq _ hj', wPt_ev (hcF _ (List.getElem_mem hj')) hy]
  obtain ⟨hlen, hplen, hw0, hp0, hdist, hcovP, hrows⟩ := locK_sound hloc
  have hd0 : 0 < d := by omega
  have hlw : 0 < lw.length := by rw [hlen]; exact Nat.mul_pos hd0 (by omega)
  have hLi : ∀ i < lw.length, ∀ y < 1755, wPt F GI lw[i]! y = ev (wEl (lw.getD i [])).1 y := by
    intro i hi y hy
    rw [getD_eq _ hi, getElem!_pos lw i hi, wPt_ev (hcL _ (List.getElem_mem hi)) hy]
  have hrow : ∀ i (hi : i < lw.length), prs.getD i 0 / d < d ∧
      prs.getD i 0 / d ≠ prs.getD i 0 % d ∧
      wEl (lw.getD i []) • (ofCode a : Vtx) = ofCode a ∧
      wEl (lw.getD i []) • (ofCode b0 : Vtx) = ofCode b0 ∧
      wEl (lw.getD i []) • ofCode (nbK lpD PL a 0) = ofCode (nbK lpD PL a (prs.getD i 0 / d)) ∧
      wEl (lw.getD i []) • ofCode (nbK lpD PL a 1) = ofCode (nbK lpD PL a (prs.getD i 0 % d)) := by
    intro i hi
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrows i hi
    have hf : ∀ y < 1755, wPt F GI lw[i] y = ev (wEl (lw.getD i [])).1 y := by
      intro y hy
      rw [← hLi i hi y hy, getElem!_pos lw i hi]
    have hm : prs.getD i 0 % d < d := Nat.mod_lt _ hd0
    exact ⟨h1, h2, (actV_iff hf ha ha).1 h3, (actV_iff hf hb0 hb0).1 h4,
      (actV_iff hf (hnbr 0 hd0).1 (hnbr _ h1).1).1 h5,
      (actV_iff hf (hnbr 1 (by omega)).1 (hnbr _ hm).1).1 h6⟩
  have hpr : ∀ i < lw.length, ∀ j < lw.length,
      wEl (lw.getD i []) = wEl (lw.getD j []) → i = j := by
    intro i hi j hj e
    obtain ⟨hi1, -, -, -, hi5, hi6⟩ := hrow i hi
    obtain ⟨hj1, -, -, -, hj5, hj6⟩ := hrow j hj
    rw [e, hj5] at hi5
    rw [e, hj6] at hi6
    have q1 := hnbi _ hj1 _ hi1 hi5
    have q2 := hnbi _ (Nat.mod_lt _ hd0) _ (Nat.mod_lt _ hd0) hi6
    have hpq : prs.getD i 0 = prs.getD j 0 := by
      rw [← Nat.div_add_mod (prs.getD i 0) d, ← Nat.div_add_mod (prs.getD j 0) d, q1, q2]
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdist j (by omega) i h hpq.symm
    · exact hdist i (by omega) j h hpq
  refine ⟨ofCode b0, ofCode (nbK lpD PL a 0), ofCode (nbK lpD PL a 1),
    (fun j => wEl (fw.getD j [])) '' {j | j < k},
    (Finset.range lw.length).image (fun i => wEl (lw.getD i [])), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hnG, hcnt, ?_, ?_, (hnbr 0 hd0).2, (hnbr 1 (by omega)).2, ?_, ?_,
    hpow, hodd⟩
  ·
    rintro f ⟨j, hj, rfl⟩
    obtain ⟨h1, h2⟩ := fixV_sound (allN_iff'.1 hfix j hj)
    refine ⟨(actV_iff (hAj j hj) ha ha).1 h1, fun w hw => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hadjA w hw
    have hn := (hnbr i hi).1
    exact (actV_iff (hAj j hj) hn hn).1 (h2 i (hdeg ▸ hi))
  ·
    intro b hb
    have h8 : layAt LAY (vCode b) = 8 := by rw [← hL.dist_eq b]; exact hb
    obtain ⟨g, hg, e⟩ := rec_reach (c := ofCode) (a := fun j => wEl (fw.getD j []))
      (S := (fun j => wEl (fw.getD j [])) '' {j | j < k}) (fun j hj => ⟨j, hj, rfl⟩)
      (fun j hj y x hy hx h => (actV_iff (hAj j hj) hy hx).1 h) hrec (vCode b) (vCode_lt b) h8
    exact ⟨g, hg, by rw [e, ofCode_vCode]⟩
  ·
    rw [hL.dist_eq]
    change layAt LAY (vCode (ofCode b0)) = 8
    rw [vCode_ofCode hb0]
    exact hb8
  ·
    intro h hh
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hh
    obtain ⟨-, -, h3, h4, -, -⟩ := hrow i (Finset.mem_range.1 hi)
    exact ⟨h3, h4⟩
  ·
    intro h hh hne1
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hh
    have hi' := Finset.mem_range.1 hi
    by_contra! hall
    obtain ⟨h1, h2, -, -, h5, h6⟩ := hrow i hi'
    rw [hall _ (hnbr 0 hd0).2] at h5
    rw [hall _ (hnbr 1 (by omega)).2] at h6
    have q1 := hnbi _ hd0 _ h1 h5
    have q2 := hnbi _ (by omega) _ (Nat.mod_lt _ hd0) h6
    have hp1 : prs.getD i 0 = 1 := by
      rw [← Nat.div_add_mod (prs.getD i 0) d, ← q1, ← q2]
      simp
    have hp1' : prs.getD 0 0 = 1 := by
      rw [← hp0]
      cases prs with
      | nil => simp at hplen; omega
      | cons x xs => rfl
    have hi0 : i = 0 := by
      by_contra hi0
      exact hdist i (by omega) 0 (by omega) (by rw [hp1, hp1'])
    subst hi0
    apply hne1
    have : lw.getD 0 [] = [] := by
      cases lw with
      | nil => simp at hlw
      | cons x xs =>
        simp only [List.headD_cons, List.length_eq_zero_iff] at hw0
        simp [hw0]
    rw [this, wEl_nil]
  ·
    rw [Finset.card_image_of_injOn, Finset.card_range, hlen]
    · exact hcard
    · intro i hi j hj e
      exact hpr i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e
  ·
    have hset : octGraph.neighborSet (ofCode a) =
        ↑((Finset.range d).image (fun j => (ofCode (nbK lpD PL a j) : Vtx))) := by
      ext w
      simp only [SimpleGraph.mem_neighborSet, Finset.coe_image, Finset.coe_range, Set.mem_image,
        Set.mem_Iio]
      constructor
      · intro hw
        obtain ⟨j, hj, e⟩ := hadjA w hw
        exact ⟨j, hj, e⟩
      · rintro ⟨j, hj, rfl⟩
        exact (hnbr j hj).2
    rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, Finset.card_image_of_injOn,
      Finset.card_range]
    intro i hi j hj e
    exact hnbi i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e
  ·
    intro e
    have := hnbi 0 hd0 1 (by omega) e
    omega
  ·
    intro u u' hu hu' huu'
    obtain ⟨i, hi, rfl⟩ := hadjA u hu
    obtain ⟨j, hj, rfl⟩ := hadjA u' hu'
    have hij : i ≠ j := fun e => huu' (by rw [e])
    obtain ⟨n, hn, e⟩ := List.getElem_of_mem (hcovP i hi j hj hij)
    have hn' : n < lw.length := by omega
    have hpn : prs.getD n 0 = i * d + j := by rw [getD_eq _ hn, e]
    have hdiv : prs.getD n 0 / d = i := by
      rw [hpn, Nat.add_comm, Nat.add_mul_div_right _ _ hd0, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : prs.getD n 0 % d = j := by
      rw [hpn, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    obtain ⟨-, -, -, -, h5, h6⟩ := hrow n hn'
    refine ⟨wEl (lw.getD n []), Finset.mem_image.2 ⟨n, Finset.mem_range.2 hn', rfl⟩, ?_, ?_⟩
    · rw [h5, hdiv]
    · rw [h6, hmod]

theorem ptTrans (p : Fin 1755) : ∃ g : ↥TA, g • (Sum.inl 0 : Vtx) = Sum.inl p := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.RuRank3.titsA_pretransitive.exists_smul_eq 0 p
  exact ⟨g, by rw [smul_inl]; exact congrArg Sum.inl hg⟩

theorem card_stab_pt' : Nat.card (MulAction.stabilizer ↥TA (Sum.inl 0 : Vtx)) = 20480 := by
  have horb : MulAction.orbit ↥TA (Sum.inl 0 : Vtx) = Set.range Sum.inl := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1 0, rfl⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨g, hg⟩ := ptTrans p
      exact ⟨g, hg⟩
  have h1 := card_stabilizer_mul_ncard_orbit (G := ↥TA) (Sum.inl 0 : Vtx)
  rw [horb, card_titsA] at h1
  have h2 : (Set.range (Sum.inl : Fin 1755 → Vtx)).ncard = 1755 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [h2] at h1
  omega

theorem dPt : ∃ (b₀ w₀ w₁ : Vtx) (Fg : Set ↥TA) (L : Finset ↥TA),
    LocalData ↥TA octGraph 8 (Sum.inl 0) b₀ w₀ w₁ Fg L 20480 1024 5 := by
  obtain ⟨hl5, -, hc1, -, hc3, -⟩ := dWords
  have := localData_at (a := 0) (b0 := 87) (d := 5) (k := 5) (cnt := 1024) (nG := 20480)
    (by norm_num) (by norm_num) hl5 hc1 hc3 bindP fix0 rec0 lay0 (farK_sound far).1 loc0
    (by rw [degK_eq]; norm_num) (by rw [ofCode_zero]; exact card_stab_pt') (by norm_num)
    ⟨12, by norm_num⟩ (by decide) (by norm_num)
  rwa [ofCode_zero] at this

theorem onLine00 : onLine lpD 0 0 = true := by decide +kernel

theorem lnTrans (v : Fin 2925) : ∃ g : ↥TA, g • (Sum.inr 0 : Vtx) = Sum.inr v := by
  obtain ⟨b₀, w₀, w₁, Fg, L, D⟩ := dPt
  have horb := D.orbit_nbr
  have hp : titsLinePt v 0 ∈ titsLine v := RuType.J47.linePt_mem v (by norm_num)
  obtain ⟨g, hg⟩ := ptTrans (titsLinePt v 0)
  have hadj : octGraph.Adj (Sum.inl 0) (g⁻¹ • (Sum.inr v : Vtx)) := by
    have := (GraphAction.adj_smul (Γ := octGraph) g⁻¹ (Sum.inl (titsLinePt v 0) : Vtx)
      (Sum.inr v)).2 (octGraph_adj_inl_inr.2 hp)
    rwa [← hg, inv_smul_smul] at this
  have hadj0 : octGraph.Adj (Sum.inl 0 : Vtx) (Sum.inr 0) := (onLine_mem 0 0).1 onLine00
  have h1 : g⁻¹ • (Sum.inr v : Vtx) ∈ MulAction.orbit (MulAction.stabilizer ↥TA (Sum.inl 0 : Vtx)) w₀ := by
    rw [horb]
    exact hadj
  have h2 : (Sum.inr 0 : Vtx) ∈ MulAction.orbit (MulAction.stabilizer ↥TA (Sum.inl 0 : Vtx)) w₀ := by
    rw [horb]
    exact hadj0
  obtain ⟨s, hs⟩ := h1
  obtain ⟨s', hs'⟩ := h2
  refine ⟨g * s.1 * s'.1⁻¹, ?_⟩
  have e1 : s'.1⁻¹ • (Sum.inr 0 : Vtx) = w₀ := by
    rw [inv_smul_eq_iff]
    exact hs'.symm
  have hs2 : (s : ↥TA) • w₀ = g⁻¹ • (Sum.inr v : Vtx) := hs
  rw [mul_smul, mul_smul, e1, hs2, smul_inv_smul]

theorem card_stab_ln' : Nat.card (MulAction.stabilizer ↥TA (Sum.inr 0 : Vtx)) = 12288 := by
  have horb : MulAction.orbit ↥TA (Sum.inr 0 : Vtx) = Set.range Sum.inr := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨titsLineHom g 0, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨g, hg⟩ := lnTrans v
      exact ⟨g, hg⟩
  have h1 := card_stabilizer_mul_ncard_orbit (G := ↥TA) (Sum.inr 0 : Vtx)
  rw [horb, card_titsA] at h1
  have h2 : (Set.range (Sum.inr : Fin 2925 → Vtx)).ncard = 2925 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [h2] at h1
  omega

theorem dLn : ∃ (b₀ w₀ w₁ : Vtx) (Fg : Set ↥TA) (L : Finset ↥TA),
    LocalData ↥TA octGraph 8 (Sum.inr 0) b₀ w₀ w₁ Fg L 12288 2048 3 := by
  obtain ⟨-, hl3, -, hc2, -, hc4⟩ := dWords
  have := localData_at (a := 1755) (b0 := 1862) (d := 3) (k := 3) (cnt := 2048) (nG := 12288)
    (by norm_num) (by norm_num) hl3 hc2 hc4 bindL fix1 rec1 lay1 lay1862 loc1
    (by rw [degK_eq]; norm_num) (by rw [ofCode_1755]; exact card_stab_ln') (by norm_num)
    ⟨12, by norm_num⟩ (by decide) (by norm_num)
  rwa [ofCode_1755] at this

theorem vcover (x : Vtx) : ∃ g : ↥TA, g • (Sum.inl 0 : Vtx) = x ∨ g • (Sum.inr 0 : Vtx) = x := by
  cases x with
  | inl p =>
    obtain ⟨g, hg⟩ := ptTrans p
    exact ⟨g, Or.inl hg⟩
  | inr v =>
    obtain ⟨g, hg⟩ := lnTrans v
    exact ⟨g, Or.inr hg⟩

theorem layAll : ∀ x : Vtx, ∃ lay, Layers octGraph 8 x lay := by
  have h0 := (lay_at lay0).1
  have h1 := (lay_at lay1).1
  rw [ofCode_zero] at h0
  rw [ofCode_1755] at h1
  exact layers_of_cover h0 h1 vcover

theorem poly : IsGenPolygon octGraph 8 := by
  have h0 := (lay_at lay0).1
  rw [ofCode_zero] at h0
  obtain ⟨hcs, hc'⟩ := cycK_sound cyc
  have hlt : ∀ i < 16, CYC.getD i 0 < 4680 := fun i hi => (adjK_iff.1 (hc' i hi).1).2.1
  have hmod : ∀ i : ℕ, ((i + 1) % 16) = (i % 16 + 1) % 16 := fun i => by omega
  have hmod2 : ∀ i : ℕ, ((i + 2) % 16) = (i % 16 + 2) % 16 := fun i => by omega
  obtain ⟨b₁, w₁₀, w₁₁, Fg₁, L₁, D₁⟩ := dPt
  obtain ⟨b₂, w₂₀, w₂₁, Fg₂, L₂, D₂⟩ := dLn
  refine isGenPolygon_of_layers (by norm_num) (fun x => x.isRight) ?_ layAll
    ⟨Sum.inl 0, _, ofCode 87, h0, ?_⟩ (fun i => ofCode (CYC.getD (i % 16) 0)) ?_ ?_ ?_ ?_
  · intro x y h
    cases x <;> cases y <;> first | exact h.elim | simp
  · change layAt LAY0 (vCode (ofCode 87)) = 8
    rw [vCode_ofCode (by norm_num)]
    exact (farK_sound far).1
  · intro i
    have hi := Nat.mod_lt i (show 0 < 16 by norm_num)
    have h1 := (hc' (i % 16) hi).1
    rw [adj_iff, vCode_ofCode (hlt _ hi), vCode_ofCode (hlt _ (Nat.mod_lt _ (by norm_num))), hmod]
    exact h1
  · intro i e
    have hi := Nat.mod_lt i (show 0 < 16 by norm_num)
    have e' := congrArg vCode e
    rw [vCode_ofCode (hlt _ hi), vCode_ofCode (hlt _ (Nat.mod_lt _ (by norm_num))), hmod2] at e'
    exact (hc' (i % 16) hi).2 e'
  · intro i
    change ofCode (CYC.getD ((i + 16) % 16) 0) = ofCode (CYC.getD (i % 16) 0)
    rw [Nat.add_mod_right]
  · intro x
    obtain ⟨g, hg | hg⟩ := vcover x
    · rw [← hg, encard_neighborSet_smul]
      exact two_le_encard D₁.adj0 D₁.adj1 D₁.ne01
    · rw [← hg, encard_neighborSet_smul]
      exact two_le_encard D₂.adj0 D₂.adj1 D₂.ne01

theorem facts : IsGenPolygon octGraph 8 ∧ (∀ x : Vtx, ∃ lay, Layers octGraph 8 x lay) ∧
    (∃ (b₀ w₀ w₁ : Vtx) (Fg : Set ↥TA) (L : Finset ↥TA),
      LocalData ↥TA octGraph 8 (Sum.inl 0) b₀ w₀ w₁ Fg L 20480 1024 5) ∧
    (∃ (b₀ w₀ w₁ : Vtx) (Fg : Set ↥TA) (L : Finset ↥TA),
      LocalData ↥TA octGraph 8 (Sum.inr 0) b₀ w₀ w₁ Fg L 12288 2048 3) ∧
    ∀ v : Fin 2925, ∃ g : ↥TA, g • (Sum.inr 0 : Vtx) = Sum.inr v :=
  ⟨poly, layAll, dPt, dLn, lnTrans⟩

end CertificateChecks.KernelTitsOct

end
