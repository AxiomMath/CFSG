module

public import Certificates.Kernel.McLMult.Cover
public import Certificates.Kernel.McLCover.TabsA
public import CFSG.Certificates.Kernel.McLMultSound
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Sporadic.Recognition.McLMultiplierMats

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLMult

open CFSG.F3.Native CFSG.KS.F3R CFSG.KS.F3L CFSG.KC.McLMult CFSG.KC.MiscCoset CFSG.CosetTable
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.McLMultiplier CFSG.Sporadic.McL

theorem mt_A : mt 21 (laneOf SA.chars) = mA := by
  unfold CFSG.KC.McLMult.mt
  rw [← rowsOf_seed seedA_ok, ← SA.eq]
  exact toMat_matA

theorem mt_B : mt 21 (laneOf SB.chars) = mB := by
  unfold CFSG.KC.McLMult.mt
  rw [← rowsOf_seed seedB_ok, ← SB.eq]
  exact toMat_matB

theorem wf_A : WF 21 (laneOf SA.chars) := by
  unfold WF
  rw [← rowsOf_seed seedA_ok]
  exact RowsWF.rowsOf 21 _

theorem wf_B : WF 21 (laneOf SB.chars) := by
  unfold WF
  rw [← rowsOf_seed seedB_ok]
  exact RowsWF.rowsOf 21 _

theorem id21 : IdL 21 (idLane 21) := idL_of id21_ok

noncomputable abbrev B4 : V :=
  powLane 21 (spreadE 21 21) (idLane 21) (laneOf SB.chars) 4

noncomputable abbrev Ys : List V :=
  ysOf 21 (spreadE 21 21) (idLane 21) (laneOf SA.chars) (laneOf SB.chars) B4

theorem wf_B4 : WF 21 B4 := (mt_powLane (by norm_num) id21 wf_B 4).1

theorem mt_B4 : mt 21 B4 = mB ^ 4 := by
  rw [(mt_powLane (by norm_num) id21 wf_B 4).2, mt_B]

theorem at6_Ys {k : ℕ} (hk : k < 6) :
    at6 Ys k = abK 21 (spreadE 21 21) (idLane 21) (laneOf SA.chars) (laneOf SB.chars) B4
      (mclGenWord k) := by
  rw [at6_eq _ (by simp [ysOf]; exact hk)]
  simp [ysOf]

theorem Ys_spec {k : ℕ} (hk : k < 6) : WF 21 (at6 Ys k) ∧ mt 21 (at6 Ys k) = mclY k := by
  rw [at6_Ys hk]
  obtain ⟨h1, h2⟩ := abK_spec (by norm_num) id21 wf_A wf_B wf_B4 (mclGenWord k)
  refine ⟨h1, ?_⟩
  rw [h2, mt_A, mt_B, mt_B4]
  rfl

theorem gen_facts :
    (∀ r ∈ mclRels, evalK 21 (spreadE 21 21) (idLane 21) (at6 Ys) (at6 Ys) r = idLane 21) ∧
      (∀ i : Fin 6, evalK 21 (spreadE 21 21) (idLane 21) (at6 Ys) (at6 Ys) (mclCommWord i) =
        at6 Ys i.val) ∧
      evalK 21 (spreadE 21 21) (idLane 21) (at6 Ys) (at6 Ys) mclSurjA = laneOf SA.chars ∧
      evalK 21 (spreadE 21 21) (idLane 21) (at6 Ys) (at6 Ys) mclSurjB = laneOf SB.chars := by
  have h := gen_ok
  unfold genAB at h
  simp only [strictT_eq, strictV_eq, strictLs_eq] at h
  exact genCheck_spec h

theorem mt_evalY (w : List (Fin 6 × Bool)) :
    mt 21 (evalK 21 (spreadE 21 21) (idLane 21) (at6 Ys) (at6 Ys) w) = mclEvalY w := by
  rw [(evalK_spec (by norm_num) id21 (fun k hk => (Ys_spec hk).1) (fun k hk => (Ys_spec hk).1)
    w).2]
  unfold mclEvalY
  congr 1
  apply List.map_congr_left
  intro l _
  rw [ite_self, (Ys_spec l.1.isLt).2]

theorem mclEvalY_rels : ∀ r ∈ mclRels, mclEvalY r = 1 := fun r hr => by
  rw [← mt_evalY, gen_facts.1 r hr, id21.mt]

theorem mclEvalY_comm (i : Fin 6) : mclEvalY (mclCommWord i) = mclY i := by
  rw [← mt_evalY, gen_facts.2.1 i, (Ys_spec i.isLt).2]

theorem mclEvalY_surjA : mclEvalY mclSurjA = mA := by
  rw [← mt_evalY, gen_facts.2.2.1, mt_A]

theorem mclEvalY_surjB : mclEvalY mclSurjB = mB := by
  rw [← mt_evalY, gen_facts.2.2.2, mt_B]

theorem relsA_eq : mclCover.map encW = CFSG.KBRoute.F6107a.rels := by
  decide +kernel

theorem wordsA_eq : (subsetOf 6 [0, 1, 2, 3, 5]).map (fun x => [(x.val, true)]) =
    CFSG.KBRoute.F6107a.T1.words := by
  decide +kernel

theorem relsB_eq : (restrictWords (subsetOf 6 [0, 1, 2, 3, 5]) mclCover).map encW =
    CFSG.KBRoute.F6107b.rels := by
  decide +kernel

theorem wordsB_eq : CFSG.KBRoute.F6107b.T1.words = [] := by
  decide +kernel

theorem card_mclCover_le : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000 := by
  have ha := CFSG.KBFact.F6107a
  have hb := CFSG.KBFact.F6107b
  rw [← relsA_eq, ← wordsA_eq] at ha
  rw [← relsB_eq, wordsB_eq] at hb
  have h := TableFact.card_restrict mclCover (by norm_num) (subsetOf 6 [0, 1, 2, 3, 5])
    (by decide) ha hb
  change Finite (PresentedGroup (coverRelators (wordSet mclRels) mclCommW)) ∧
    Nat.card (PresentedGroup (coverRelators (wordSet mclRels) mclCommW)) ≤ 2694384000
  have e : coverRelators (wordSet mclRels) mclCommW = wordSet mclCover :=
    coverRelators_wordSet mclRels mclCommWord
  rw [e]
  exact h

theorem id42 : IdL 42 (idLane 42) := idL_of id42_ok

theorem canon_id42 : Canon 42 (idLane 42) := by
  have h := id42_ok
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact canonL_spec h.1

noncomputable abbrev Ys42 : List V :=
  ysOf 42 (spreadE 42 42) (idLane 42) (laneOf TA.chars) (laneOf TB.chars)
    (powLane 42 (spreadE 42 42) (idLane 42) (laneOf TB.chars) 4)

noncomputable abbrev Yis42 : List V :=
  yisOf 42 (spreadE 42 42) (idLane 42) (laneOf TA.chars) (laneOf TB.chars)
    (powLane 42 (spreadE 42 42) (idLane 42) (laneOf TB.chars) 4)

noncomputable abbrev Es : List V := esOf 42 (spreadE 42 42) (idLane 42) Ys42 Yis42

noncomputable abbrev Eis : List V := eisOf 42 (spreadE 42 42) (idLane 42) Ys42 Yis42

noncomputable abbrev evE (w : List (Fin 6 × Bool)) : V :=
  evalK 42 (spreadE 42 42) (idLane 42) (at6 Es) (at6 Eis) w

theorem cover_facts :
    (∀ i < 6, Canon 42 (at6 Es i) ∧ Canon 42 (at6 Eis i) ∧
        mulL 42 (spreadE 42 42) (at6 Es i) (at6 Eis i) = idLane 42 ∧
        mulL 42 (spreadE 42 42) (at6 Eis i) (at6 Es i) = idLane 42) ∧
      (∀ r ∈ mclRels, ∀ j < 6, mulL 42 (spreadE 42 42) (at6 Es j) (evE r) =
        mulL 42 (spreadE 42 42) (evE r) (at6 Es j)) ∧
      (∀ i : Fin 6, evE (mclCommWord i) = at6 Es i.val) ∧
      Canon 42 (evE mclR0) ∧ evE mclR0 ≠ idLane 42 ∧
      mulL 42 (spreadE 42 42) (evE mclR0) (mulL 42 (spreadE 42 42) (evE mclR0) (evE mclR0)) =
        idLane 42 := by
  have h := cover_ok
  unfold coverAB withEs at h
  simp only [strictT_eq, strictV_eq, strictLs_eq] at h
  exact coverCheck_spec h

theorem wf_Es {k : ℕ} (hk : k < 6) : WF 42 (at6 Es k) := (cover_facts.1 k hk).1.wF

theorem wf_Eis {k : ℕ} (hk : k < 6) : WF 42 (at6 Eis k) := (cover_facts.1 k hk).2.1.wF

theorem evE_spec (w : List (Fin 6 × Bool)) : WF 42 (evE w) ∧ mt 42 (evE w) =
    (w.map fun l => if l.2 then mt 42 (at6 Es l.1.val) else mt 42 (at6 Eis l.1.val)).prod :=
  evalK_spec (by norm_num) id42 (fun _ hk => wf_Es hk) (fun _ hk => wf_Eis hk) w

theorem mt_mul_inv {k : ℕ} (hk : k < 6) : mt 42 (at6 Es k) * mt 42 (at6 Eis k) = 1 := by
  rw [← mt_mulL (by norm_num) (wf_Es hk) (wf_Eis hk), (cover_facts.1 k hk).2.2.1, id42.mt]

theorem mt_inv_mul {k : ℕ} (hk : k < 6) : mt 42 (at6 Eis k) * mt 42 (at6 Es k) = 1 := by
  rw [← mt_mulL (by norm_num) (wf_Eis hk) (wf_Es hk), (cover_facts.1 k hk).2.2.2, id42.mt]

noncomputable def gE (i : Fin 6) : GL (Fin 42) (ZMod 3) :=
  ⟨mt 42 (at6 Es i.val), mt 42 (at6 Eis i.val), mt_mul_inv i.isLt, mt_inv_mul i.isLt⟩

theorem val_lift_mk {n : Type} [Fintype n] [DecidableEq n] {R : Type} [CommRing R]
    (g : Fin 6 → GL n R) (w : List (Fin 6 × Bool)) :
    ((FreeGroup.lift g (FreeGroup.mk w) : GL n R) : Matrix n n R) =
      (w.map fun l => if l.2 then ((g l.1 : GL n R) : Matrix n n R)
        else (((g l.1)⁻¹ : GL n R) : Matrix n n R)).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    rw [e, map_mul, Units.val_mul, ih, List.map_cons, List.prod_cons]
    obtain ⟨i, b⟩ := l
    cases b
    · have e1 : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
      rw [e1, map_inv, FreeGroup.lift_apply_of]
      rfl
    · have e1 : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
      rw [e1, FreeGroup.lift_apply_of]
      rfl

theorem val_lift_gE (w : List (Fin 6 × Bool)) :
    ((FreeGroup.lift gE (FreeGroup.mk w) : GL (Fin 42) (ZMod 3)) :
      Matrix (Fin 42) (Fin 42) (ZMod 3)) = mt 42 (evE w) := by
  rw [val_lift_mk, (evE_spec w).2]
  rfl

theorem lift_gE_rels : ∀ r ∈ coverRelators (wordSet mclRels) mclCommW, FreeGroup.lift gE r = 1 := by
  rintro _ (⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩)
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
    rw [map_commutatorElement, FreeGroup.lift_apply_of, commutatorElement_eq_one_iff_mul_comm]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, val_lift_gE]
    change mt 42 (at6 Es i.val) * _ = _ * mt 42 (at6 Es i.val)
    rw [← mt_mulL (by norm_num) (wf_Es i.isLt) (evE_spec v).1,
      ← mt_mulL (by norm_num) (evE_spec v).1 (wf_Es i.isLt), cover_facts.2.1 v hv i.val i.isLt]
  · rw [map_mul, map_inv, FreeGroup.lift_apply_of, inv_mul_eq_one]
    apply Units.ext
    change _ = ((FreeGroup.lift gE (FreeGroup.mk (mclCommWord i)) : GL (Fin 42) (ZMod 3)) :
      Matrix (Fin 42) (Fin 42) (ZMod 3))
    rw [val_lift_gE, cover_facts.2.2.1 i]
    rfl

theorem three_dvd_orderOf_mclR0 :
    3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover) := by
  obtain ⟨-, -, -, hc, hne, h3⟩ := cover_facts
  have hw := (evE_spec mclR0).1
  let φ : MclCover →* GL (Fin 42) (ZMod 3) := PresentedGroup.toGroup lift_gE_rels
  have hz : (φ (PresentedGroup.mk _ (FreeGroup.mk mclR0)) : Matrix (Fin 42) (Fin 42) (ZMod 3)) =
      mt 42 (evE mclR0) := val_lift_gE mclR0
  have hcube : φ (PresentedGroup.mk _ (FreeGroup.mk mclR0)) ^ 3 = 1 := by
    apply Units.ext
    rw [pow_three, Units.val_mul, Units.val_mul, hz, ← mt_mulL (by norm_num) hw hw,
      ← mt_mulL (by norm_num) hw (wf_mulL (by norm_num) hw hw), h3, id42.mt, Units.val_one]
  have hne1 : φ (PresentedGroup.mk _ (FreeGroup.mk mclR0)) ≠ 1 := by
    intro e
    have e' := congrArg (fun x : GL (Fin 42) (ZMod 3) => (x : Matrix (Fin 42) (Fin 42) (ZMod 3))) e
    simp only [Units.val_one] at e'
    rw [hz, ← id42.mt] at e'
    exact mt_ne hc canon_id42 hne e'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord := orderOf_eq_prime hcube hne1
  rw [← hord]
  exact orderOf_map_dvd φ _

end CertificateChecks.KernelMcLMult

end
