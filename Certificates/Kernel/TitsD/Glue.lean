module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoDAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLoc
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLnLoc
public import Certificates.Kernel.TitsF48.Glue
public import CFSG.Certificates.Kernel.TitsDSound
public import Certificates.Certificate4190Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsD

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TwoF4LieSound
  CFSG.KC.TitsOctSound CFSG.KC.TitsDK CFSG.KC.TitsDSound CFSG.Sporadic.Schreier.Tits
  CFSG.Quasithin CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.TitsGeo CertificateChecks.KernelMisc
  CertificateChecks.KernelTitsOct CertificateChecks.KernelTitsF48

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem lpT_eq : lpT = lpD := rfl

theorem FH_eq : FH = HG := rfl

theorem adj_nb {a : ℕ} (ha : a < 4680) (u : Vtx) :
    octGraph.Adj (ofCode a) u ↔ ∃ k < degK a, nbK lpD CFSG.KD.TitsOct.PL a k = vCode u := by
  rw [adj_iff, vCode_ofCode ha]
  exact nbOK.1 a ha (vCode u)

theorem nb_lt {a k : ℕ} (ha : a < 4680) (hk : k < degK a) :
    nbK lpD CFSG.KD.TitsOct.PL a k < 4680 :=
  (adjK_iff.1 ((nbOK.1 a ha _).2 ⟨k, hk, rfl⟩)).1

theorem adj_of_nb {a k : ℕ} (ha : a < 4680) (hk : k < degK a) :
    octGraph.Adj (ofCode a) (ofCode (nbK lpD CFSG.KD.TitsOct.PL a k)) :=
  (adj_nb ha _).2 ⟨k, hk, (vCode_ofCode (nb_lt ha hk)).symm⟩

theorem actD' {x : Pm} (hx : x ∈ titsD) {f : ℕ → ℕ} (hf : ∀ y < 1755, f y = ev x y) {y z : ℕ}
    (hy : y < 4680) (hz : z < 4680) :
    actV lpD f y z = true ↔ (⟨x, hx⟩ : ↥titsD) • ofCode y = ofCode z :=
  actV_iff (g := ⟨x, titsD_le_titsA hx⟩) hf hy hz

theorem lay0_dist : Layers octGraph 8 (Sum.inl 0) (fun x => layAt CFSG.KD.TitsOct.LAY0 (vCode x)) := by
  have h := (lay_at lay0).1
  rwa [ofCode_zero] at h

theorem lay1_dist :
    Layers octGraph 8 (Sum.inr 0) (fun x => layAt CFSG.KD.TitsOct.LAY1 (vCode x)) := by
  have h := (lay_at lay1).1
  rwa [ofCode_1755] at h

theorem lays : layAt CFSG.KD.TitsOct.LAY0 87 = 8 ∧ layAt CFSG.KD.TitsOct.LAY1 45 = 7 ∧
    layAt CFSG.KD.TitsOct.LAY1 1862 = 8 ∧ layAt CFSG.KD.TitsOct.LAY1 1896 = 8 := by
  have h := layP
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1,
    Nat.eq_of_beq_eq_true h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem lett_prepM {m : ℕ} {F FI : ℕ → ℕ} {g : ℕ → Pm} (hF : ∀ j < m, PR (F j) (g j))
    (hFI : ∀ j < m, PR (FI j) (g j)⁻¹) {c : ℕ} (hc : 2 ≤ c) (hc' : c < 2 * m + 2) :
    PR (lett F FI c) (letP g c) := by
  rw [lett_eq']
  unfold letP
  split_ifs
  · exact hF _ (by omega)
  · exact hFI _ (by omega)

theorem wPtM {m : ℕ} {F FI : ℕ → ℕ} {g : ℕ → Pm} (hF : ∀ j < m, PR (F j) (g j))
    (hFI : ∀ j < m, PR (FI j) (g j)⁻¹) :
    ∀ wd : List ℕ, (∀ c ∈ wd, 2 ≤ c ∧ c < 2 * m + 2) →
      ∀ x : Fin 1755, wPt F FI wd x = (wordP g wd x : ℕ)
  | [], _, x => by simp [wordP, wPt]
  | c :: wd, hw, x => by
    have h1 := lett_prepM hF hFI (hw c List.mem_cons_self).1 (hw c List.mem_cons_self).2
    have h2 := wPtM hF hFI wd (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) x
    have e : wPt F FI (c :: wd) x = gp (lett F FI c) (wPt F FI wd x) := strictN_eq' _ _
    rw [e, h2, gp_eq h1 (wordP g wd x)]
    simp [wordP, Equiv.Perm.mul_apply]

theorem wordM_mem {m : ℕ} {S : Subgroup Pm} {g : ℕ → Pm} (hg : ∀ j < m, g j ∈ S) {wd : List ℕ}
    (hw : ∀ c ∈ wd, 2 ≤ c ∧ c < 2 * m + 2) : wordP g wd ∈ S := by
  unfold wordP
  refine Subgroup.list_prod_mem (K := S) ?_
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  have hm : c / 2 - 1 < m := by have := hw c hc; omega
  unfold letP
  split_ifs
  · exact hg _ hm
  · exact Subgroup.inv_mem _ (hg _ hm)

theorem getD_mem' {l : List (List ℕ)} {i : ℕ} (hi : i < l.length) : l.getD i [] ∈ l := by
  rw [getD_eq [] hi]
  exact List.getElem_mem hi

theorem bind_ev {m : ℕ} {F FI E : ℕ → ℕ} {g : ℕ → Pm} (hF : ∀ j < m, PR (F j) (g j))
    (hFI : ∀ j < m, PR (FI j) (g j)⁻¹) {ws : List (List ℕ)} (hb : bindK F FI E ws = true)
    (hw : ∀ w ∈ ws, ∀ c ∈ w, 2 ≤ c ∧ c < 2 * m + 2) {i : ℕ} (hi : i < ws.length) :
    ∀ y < 1755, gp (E i) y = ev (wordP g (ws.getD i [])) y := by
  intro y hy
  rw [bindK_sound hb i hi y hy, ← getD_eq [] hi,
    wPtM hF hFI _ (hw _ (getD_mem' hi)) ⟨y, hy⟩]
  simp [ev, hy]

theorem dW : CFSG.KD.TitsD.wPt.length = 10 ∧ CFSG.KD.TitsD.w1Ln.length = 6 ∧
    CFSG.KD.TitsD.w2Ln.length = 6 ∧
    (∀ w ∈ CFSG.KD.TitsD.wPt, ∀ c ∈ w, 2 ≤ c ∧ c < 2 * 9 + 2) ∧
    (∀ w ∈ CFSG.KD.TitsD.w1Ln, ∀ c ∈ w, 2 ≤ c ∧ c < 2 * 10 + 2) ∧
    (∀ w ∈ CFSG.KD.TitsD.w2Ln, ∀ c ∈ w, 2 ≤ c ∧ c < 2 * 10 + 2) := by
  decide +kernel

@[expose] noncomputable def gN (j : ℕ) : Pm := genPerm titsNArrs j

theorem hNG {j : ℕ} (hj : j < 10) : PR (FN j) (gN j) ∧ PR (CFSG.KD.TitsD.NI j) (gN j)⁻¹ :=
  pr_field (L₀ := 61) (m := 10) hj (by omega) (allN_iff'.1 invN j hj)

theorem gN_mem {j : ℕ} (hj : j < 10) : gN j ∈ titsN := genN_mem hj

theorem hHG' : (∀ j < 9, PR (HG j) (gH j)) ∧ ∀ j < 9, PR (CFSG.KD.TitsD.HI j) (gH j)⁻¹ :=
  ⟨fun _ hj => (hHG hj).1, fun _ hj => (hHG hj).2⟩

theorem hNG' : (∀ j < 10, PR (FN j) (gN j)) ∧ ∀ j < 10, PR (CFSG.KD.TitsD.NI j) (gN j)⁻¹ :=
  ⟨fun _ hj => (hNG hj).1, fun _ hj => (hNG hj).2⟩

@[expose] noncomputable def dOf (S : Subgroup Pm) (hS : S ≤ titsD) (x : Pm) : ↥titsD :=
  open Classical in if h : x ∈ S then ⟨x, hS h⟩ else 1

theorem dOf_eq {S : Subgroup Pm} {hS : S ≤ titsD} {x : Pm} (h : x ∈ S) :
    dOf S hS x = ⟨x, hS h⟩ := by
  simp [dOf, h]

theorem fixP {x : Pm} (h : x ∈ titsH) :
    dOf titsH titsH_le_titsD x • (Sum.inl 0 : Vtx) = Sum.inl 0 := by
  rw [dOf_eq h]
  exact fix_inl_of_mem_titsH (g := ⟨x, titsH_le_titsD h⟩) h

theorem fixL {x : Pm} (h : x ∈ titsN) :
    dOf titsN titsN_le_titsD x • (Sum.inr 0 : Vtx) = Sum.inr 0 := by
  rw [dOf_eq h]
  exact fix_inr_of_mem_titsN (g := ⟨x, titsN_le_titsD h⟩) h

theorem actOf {S : Subgroup Pm} {hS : S ≤ titsD} {x : Pm} (h : x ∈ S) {P : ℕ}
    (hP : ∀ y < 1755, gp P y = ev x y) {y z : ℕ} (hy : y < 4680) (hz : z < 4680) :
    actV lpD (gp P) y z = true ↔ dOf S hS x • ofCode y = ofCode z := by
  rw [dOf_eq h]
  exact actD' (hS h) hP hy hz

theorem reach {S : Subgroup Pm} (hS : S ≤ titsD) {v : Vtx}
    (hfix : ∀ {x : Pm}, x ∈ S → dOf S hS x • v = v) {m : ℕ} {g : ℕ → Pm} {A : ℕ → ℕ}
    (hg : ∀ j < m, g j ∈ S) (hA : ∀ j < m, PR (A j) (g j)) {isRoot : ℕ → Bool}
    {L cnt LAY ORD PR' LB PS : ℕ} (h : recR lpD A m isRoot L cnt LAY ORD PR' LB PS = true) :
    ∀ x < 4680, layAt LAY x = L → ∃ r, isRoot r = true ∧
      ∃ k : ↥titsD, k • v = v ∧ k • ofCode r = ofCode x := by
  intro x hx hL
  obtain ⟨r, hr, k, hk, e⟩ := recR_reach (c := ofCode) (a := fun j => dOf S hS (g j))
    (S := (MulAction.stabilizer ↥titsD v : Set ↥titsD))
    (fun j hj => MulAction.mem_stabilizer_iff.2 (hfix (hg j hj)))
    (fun j hj y z hy hz hv => (actOf (hg j hj) (fun _ hn => gp_ev (hA j hj) hn) hy hz).1 hv)
    h x hx hL
  rw [Subgroup.closure_eq] at hk
  exact ⟨r, hr, k, MulAction.mem_stabilizer_iff.1 hk, e⟩

@[expose] noncomputable def eP (i : ℕ) : Pm := wordP gH (CFSG.KD.TitsD.wPt.getD i [])

theorem eP_mem {i : ℕ} : eP i ∈ titsH := by
  refine wordM_mem (m := 9) (fun j hj => gH_mem hj) ?_
  intro c hc
  by_cases hi : i < CFSG.KD.TitsD.wPt.length
  · exact dW.2.2.2.1 _ (getD_mem' hi) c hc
  · rw [List.getD_eq_default _ _ (by omega)] at hc
    simp at hc

theorem eP_ev {i : ℕ} (hi : i < 10) : ∀ y < 1755, gp (CFSG.KD.TitsD.EP i) y = ev (eP i) y := by
  have b := bindP
  rw [FH_eq] at b
  exact bind_ev hHG'.1 hHG'.2 b dW.2.2.2.1 (by rw [dW.1]; exact hi)

@[expose] noncomputable def dP (i : ℕ) : ↥titsD := dOf titsH titsH_le_titsD (eP i)

theorem dP_act {i : ℕ} (hi : i < 10) {y z : ℕ} (hy : y < 4680) (hz : z < 4680) :
    actV lpD (gp (CFSG.KD.TitsD.EP i)) y z = true ↔ dP i • ofCode y = ofCode z :=
  actOf eP_mem (eP_ev hi) hy hz

theorem dP_fix {i : ℕ} (hi : i < 10) (y : ℕ) (hy : y < 4680)
    (h : actV lpD (gp (CFSG.KD.TitsD.EP i)) y y = true) : dP i • ofCode y = ofCode y :=
  (dP_act hi hy hy).1 h

theorem moves_of {E : ℕ → ℕ} {n a b : ℕ} {d : ℕ → ↥titsD} (ha : a < 4680) (hb : b < 4680)
    (hd : ∀ i < n, ∀ y < 4680, ∀ z < 4680,
      (actV lpD (gp (E i)) y z = true ↔ d i • ofCode y = ofCode z))
    (h : stabK lpD CFSG.KD.TitsOct.PL E n a b = true) :
    ∀ u, octGraph.Adj (ofCode a) u → ∃ k : ↥titsD, k • ofCode a = ofCode a ∧
      k • ofCode b = ofCode b ∧ k • u = u ∧ ∃ w, octGraph.Adj (ofCode a) w ∧ k • w ≠ w := by
  obtain ⟨hs1, hs2⟩ := stabK_sound h
  intro u hu
  obtain ⟨k, hk, hku⟩ := (adj_nb ha u).1 hu
  obtain ⟨i, hi, hfu, k', hk', hfy⟩ := hs2 k hk
  have hl := nb_lt ha hk
  have hl' := nb_lt ha hk'
  refine ⟨d i, (hd i hi a ha a ha).1 (hs1 i hi).1, (hd i hi b hb b hb).1 (hs1 i hi).2, ?_,
    ofCode (nbK lpD CFSG.KD.TitsOct.PL a k'), adj_of_nb ha hk', ?_⟩
  · rw [← ofCode_vCode u, ← hku]
    exact (hd i hi _ hl _ hl).1 hfu
  · intro hc
    have := (hd i hi _ hl' _ hl').2 hc
    rw [hfy] at this
    exact absurd this (by decide)

theorem ptLoc : PtLoc ↥titsD octGraph (Sum.inl 0) (ofCode 87) (Sum.inr 0) := by
  have hd : ∀ i < 10, ∀ y < 4680, ∀ z < 4680,
      (actV lpD (gp (CFSG.KD.TitsD.EP i)) y z = true ↔ dP i • ofCode y = ofCode z) :=
    fun i hi y hy z hz => dP_act hi hy hz
  have hst := stabP
  rw [lpT_eq] at hst
  have hz : (0 : ℕ) < 4680 := by norm_num
  have hb : (87 : ℕ) < 4680 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lay0_dist.dist_eq, vCode_ofCode hb]
    exact lays.1
  · exact (onLine_mem 0 0).1 onLine00
  · intro b hb8
    have hl : layAt CFSG.KD.TitsOct.LAY0 (vCode b) = 8 := by
      rw [← hb8, lay0_dist.dist_eq]
    have hr := recP
    rw [lpT_eq, FH_eq] at hr
    obtain ⟨r, hr', k, hk, e⟩ := reach titsH_le_titsD (fun h => fixP h) (fun j hj => gH_mem hj)
      hHG'.1 hr (vCode b) (vCode_lt b) hl
    rw [Nat.eq_of_beq_eq_true hr', ofCode_vCode] at e
    exact ⟨k, hk, e⟩
  · intro u hu
    have htr := transP
    rw [lpT_eq] at htr
    rw [← ofCode_zero] at hu
    obtain ⟨k, hk, hku⟩ := (adj_nb hz u).1 hu
    obtain ⟨i, hi, hiu⟩ := transK_sound htr k hk
    obtain ⟨hs1, -⟩ := stabK_sound hst
    refine ⟨dP i, ?_, dP_fix hi 87 hb (hs1 i hi).2, ?_⟩
    · rw [← ofCode_zero]
      exact dP_fix hi 0 hz (hs1 i hi).1
    · rw [← ofCode_1755, ← ofCode_vCode u, ← hku]
      exact (dP_act hi (by norm_num) (nb_lt hz hk)).1 hiu
  · intro u hu
    rw [← ofCode_zero] at hu ⊢
    exact moves_of hz hb hd hst u hu
  · have hex := exactP
    rw [lpT_eq] at hex
    obtain ⟨hf, hk0, hiff⟩ := exactK_sound hex
    obtain ⟨hs1, -⟩ := stabK_sound hst
    have hl := nb_lt hb hk0
    refine ⟨dP 2, ?_, dP_fix (by norm_num) 87 hb (hs1 2 (by norm_num)).2, ?_,
      ofCode (nbK lpD CFSG.KD.TitsOct.PL 87 CFSG.KD.TitsD.K0), adj_of_nb hb hk0,
      (dP_act (by norm_num) hl hl).1 ((hiff _ hk0).2 rfl), ?_⟩
    · rw [← ofCode_zero]
      exact dP_fix (by norm_num) 0 hz (hs1 2 (by norm_num)).1
    · rw [← ofCode_1755]
      exact dP_fix (by norm_num) 1755 (by norm_num) hf
    · intro y hy hky
      obtain ⟨k, hk, hky'⟩ := (adj_nb hb y).1 hy
      have hl' := nb_lt hb hk
      have hfx : actV lpD (gp (CFSG.KD.TitsD.EP 2)) (nbK lpD CFSG.KD.TitsOct.PL 87 k)
          (nbK lpD CFSG.KD.TitsOct.PL 87 k) = true :=
        (dP_act (by norm_num) hl' hl').2 (by rw [hky', ofCode_vCode]; exact hky)
      rw [← ofCode_vCode y, ← hky', (hiff k hk).1 hfx]

theorem labV_code : ∀ i : ZMod 5, CFSG.TitsF46.titsLabPt[i.val]! = labF i.val := by
  decide +kernel

theorem affLab : AffLab ↥titsD octGraph (Sum.inl 0) labV := by
  have hlk := labP
  rw [lpT_eq] at hlk
  obtain ⟨hdeg, hne, hin, hsu⟩ := labK_sound hlk
  have hz : (0 : ℕ) < 4680 := by norm_num
  have hcode : ∀ i < 5, labF i < 4680 := fun i hi => by
    obtain ⟨k, hk, e⟩ := hin i hi
    rw [e]
    exact nb_lt hz (by rw [hdeg]; exact hk)
  have hv : ∀ i : ZMod 5, labV i = ofCode (labF i.val) := fun i => by
    rw [labV, labV_code]
  have hv5 : ∀ i : ZMod 5, i.val < 5 := fun i => ZMod.val_lt i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hv, hv] at hij
    have e := congrArg vCode hij
    rw [vCode_ofCode (hcode _ (hv5 i)), vCode_ofCode (hcode _ (hv5 j))] at e
    apply ZMod.val_injective 5
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact absurd e.symm (hne _ (hv5 j) _ h)
    · exact h
    · exact absurd e (hne _ (hv5 i) _ h)
  · intro i
    rw [hv, ← ofCode_zero]
    obtain ⟨k, hk, e⟩ := hin _ (hv5 i)
    rw [e]
    exact adj_of_nb hz (by rw [hdeg]; exact hk)
  · intro u hu
    rw [← ofCode_zero] at hu
    obtain ⟨k, hk, hku⟩ := (adj_nb hz u).1 hu
    obtain ⟨i, hi, e⟩ := hsu k (by rwa [hdeg] at hk)
    refine ⟨(i : ZMod 5), ?_⟩
    rw [hv, ZMod.val_natCast_of_lt hi, e, hku, ofCode_vCode]
  · intro g hg
    have hgH : g.1 ∈ titsH := by
      rw [dsmul_inl] at hg
      exact RuType.J47.mem_titsH_of g.2 (Sum.inl.inj hg)
    have haf := affP
    rw [lpT_eq, FH_eq] at haf
    have hgens : ∀ (j : ℕ) (hj : j < 9),
        (⟨genPerm titsHArrs j, titsH_le_titsD (genH_mem hj)⟩ : ↥titsD) ∈ affSub := by
      intro j hj
      obtain ⟨hα0, hα5, hβ5, hact⟩ := affK_sound haf j hj
      set α := fw 3 CFSG.KD.TitsD.AF (2 * j)
      set β := fw 3 CFSG.KD.TitsD.AF (2 * j + 1)
      have hα' : (α : ZMod 5) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_eq_zero_iff α 5).1 h0
        exact absurd (Nat.le_of_dvd hα0 this) (by omega)
      refine ⟨(α : ZMod 5), (β : ZMod 5), hα', fun i => ?_⟩
      have hm5 : (α * i.val + β) % 5 < 5 := Nat.mod_lt _ (by norm_num)
      have := (actD' (titsH_le_titsD (genH_mem hj)) (fun _ hn => gp_ev (hHG hj).1 hn)
        (hcode _ (hv5 i)) (hcode _ hm5)).1 (hact i.val (hv5 i))
      rw [hv, hv, val_affine]
      exact this
    have hle : titsH ≤ affSub.map (Subgroup.subtype titsD) := by
      rw [titsH_eq_closure, Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨⟨genPerm titsHArrs j, titsH_le_titsD (genH_mem hj)⟩, hgens j hj, rfl⟩
    obtain ⟨y, hy, hyg⟩ := hle hgH
    have hyg' : y = g := Subtype.ext hyg
    rw [hyg'] at hy
    exact hy

@[expose] noncomputable def eL (s i : ℕ) : Pm :=
  wordP gN ((if s = 0 then CFSG.KD.TitsD.w1Ln else CFSG.KD.TitsD.w2Ln).getD i [])

theorem eL_mem {s i : ℕ} : eL s i ∈ titsN := by
  refine wordM_mem (m := 10) (fun j hj => gN_mem hj) ?_
  intro c hc
  have hw : ∀ w ∈ (if s = 0 then CFSG.KD.TitsD.w1Ln else CFSG.KD.TitsD.w2Ln), ∀ c ∈ w,
      2 ≤ c ∧ c < 2 * 10 + 2 := by
    split_ifs
    · exact dW.2.2.2.2.1
    · exact dW.2.2.2.2.2
  by_cases hi : i < (if s = 0 then CFSG.KD.TitsD.w1Ln else CFSG.KD.TitsD.w2Ln).length
  · exact hw _ (getD_mem' hi) c hc
  · rw [List.getD_eq_default _ _ (by omega)] at hc
    simp at hc

theorem lnMoves {s b : ℕ} {E : ℕ → ℕ} (hb : b < 4680)
    (hbind : bindK FN CFSG.KD.TitsD.NI E
      (if s = 0 then CFSG.KD.TitsD.w1Ln else CFSG.KD.TitsD.w2Ln) = true)
    (hst : stabK lpD CFSG.KD.TitsOct.PL E 6 1755 b = true) :
    ∀ u, octGraph.Adj (Sum.inr 0) u → ∃ k : ↥titsD, k • (Sum.inr 0 : Vtx) = Sum.inr 0 ∧
      k • ofCode b = ofCode b ∧ k • u = u ∧ ∃ w, octGraph.Adj (Sum.inr 0) w ∧ k • w ≠ w := by
  have hw : ∀ w ∈ (if s = 0 then CFSG.KD.TitsD.w1Ln else CFSG.KD.TitsD.w2Ln), ∀ c ∈ w,
      2 ≤ c ∧ c < 2 * 10 + 2 := by
    split_ifs
    · exact dW.2.2.2.2.1
    · exact dW.2.2.2.2.2
  have hlen : (if s = 0 then CFSG.KD.TitsD.w1Ln else CFSG.KD.TitsD.w2Ln).length = 6 := by
    split_ifs
    · exact dW.2.1
    · exact dW.2.2.1
  have hd : ∀ i < 6, ∀ y < 4680, ∀ z < 4680, (actV lpD (gp (E i)) y z = true ↔
      dOf titsN titsN_le_titsD (eL s i) • ofCode y = ofCode z) :=
    fun i hi y hy z hz => actOf eL_mem (bind_ev hNG'.1 hNG'.2 hbind hw (by rw [hlen]; exact hi))
      hy hz
  rw [← ofCode_1755]
  exact moves_of (by norm_num) hb hd hst

theorem lnLoc : LnLoc ↥titsD octGraph (Sum.inr 0) (ofCode 45) (ofCode 1862) (ofCode 1896) := by
  have hfix : ∀ {x : Pm}, x ∈ titsN → dOf titsN titsN_le_titsD x • (Sum.inr 0 : Vtx) = Sum.inr 0 :=
    fun h => fixL h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, D⟩ := dLn
    rw [← Nat.card_coe_set_eq]
    exact D.card_N
  · intro b hb7
    have hl : layAt CFSG.KD.TitsOct.LAY1 (vCode b) = 7 := by
      rw [← hb7, lay1_dist.dist_eq]
    have hr := recS
    rw [lpT_eq] at hr
    obtain ⟨r, hr', k, hk, e⟩ := reach titsN_le_titsD hfix (fun j hj => gN_mem hj) hNG'.1 hr
      (vCode b) (vCode_lt b) hl
    rw [Nat.eq_of_beq_eq_true hr', ofCode_vCode] at e
    exact ⟨k, hk, e⟩
  · intro b hb8
    have hl : layAt CFSG.KD.TitsOct.LAY1 (vCode b) = 8 := by
      rw [← hb8, lay1_dist.dist_eq]
    have hr := recE
    rw [lpT_eq] at hr
    obtain ⟨r, hr', k, hk, e⟩ := reach titsN_le_titsD hfix (fun j hj => gN_mem hj) hNG'.1 hr
      (vCode b) (vCode_lt b) hl
    rw [ofCode_vCode] at e
    rw [bIf_d] at hr'
    split_ifs at hr' with h1
    · left
      rw [Nat.eq_of_beq_eq_true h1] at e
      exact ⟨k, hk, e⟩
    · right
      rw [Nat.eq_of_beq_eq_true hr'] at e
      exact ⟨k, hk, e⟩
  · have hst := stab1
    rw [lpT_eq] at hst
    exact lnMoves (s := 0) (by norm_num) (by simpa using bind1) hst
  · have hst := stab2
    rw [lpT_eq] at hst
    exact lnMoves (s := 1) (by norm_num) (by simpa using bind2) hst

theorem facts4190 : Certificates.titsGeoFacts :=
  ⟨ptLoc, ⟨labV, affLab⟩, lnLoc, poly⟩

end CertificateChecks.KernelTitsD

end
