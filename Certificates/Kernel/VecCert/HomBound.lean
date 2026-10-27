module

public import Certificates.Kernel.Sporadic.OrdCommon
public import CFSG.Sporadic.HS.Group
public import CFSG.Sporadic.Bridge.Common
import CFSG.Certificates.Kernel.Spor.OrdCanon
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CertificateChecks.KernelVec

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge

@[expose] def rootSet (d w S Lg : Nat) (RB : Nat → Nat) : Set (Matrix (Fin d) (Fin d) (ZMod 2)) :=
  {M | ∃ g, 0 < g ∧ g ≤ 2 * Lg ∧ M = ordMat 2 d w S (RB g)}

@[expose] def RegsIn (d w S nb L H Lg : Nat) (RB : Nat → Nat) (s : Nat) : Prop :=
  ∀ r, 0 < r → r < s → validM 2 nb L H (RB r) = true ∧
    ordMat 2 d w S (RB r) ∈ Submonoid.closure (rootSet d w S Lg RB)

private theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true :=
  (andB_iff a b).1 h

private theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem brec_pres {Q : Nat → Prop} {x y : Nat} (c : Bool) (hx : Q x) (hy : Q y) :
    Q (Bool.rec (motive := fun _ => Nat) x y c) := by
  cases c
  · exact hx
  · exact hy

private theorem nrec_pres {Q : Nat → Prop} {x : Nat} {s : Nat → Nat → Nat} (hx : Q x)
    (hs : ∀ i a, Q a → Q (s i a)) : ∀ m, Q (Nat.rec (motive := fun _ => Nat) x s m)
  | 0 => hx
  | m + 1 => hs m _ (nrec_pres hx hs m)

private theorem powR_pres {Q : Nat → Prop} {mul : Nat → Nat → Nat} {ONE M : Nat} (e : Nat)
    (hmul : ∀ A B, Q A → Q B → Q (mul A B)) (hone : Q ONE) (hM : Q M) :
    Q (powR mul ONE M e) := by
  unfold powR
  generalize (nat_lit 16) = m
  apply nrec_pres hone
  intro i a ha
  rw [strictN_eq']
  have hsq := brec_pres (Q := Q) (Nat.beq a ONE) (hmul a a ha ha) ha
  exact brec_pres _ hsq (brec_pres _ (hmul _ _ hsq hM) hM)

private theorem inv_mem_of_finite {M : Type*} [Monoid M] [Finite M] {C : Submonoid M} {x y : M}
    (hx : x ∈ C) (hxy : x * y = 1) (hyx : y * x = 1) : y ∈ C := by
  let u : Mˣ := ⟨x, y, hxy, hyx⟩
  have : Finite Mˣ := Finite.of_injective (fun v : Mˣ => (v : M)) Units.val_injective
  have hpos := (isOfFinOrder_of_finite u).orderOf_pos
  have e : u⁻¹ = u ^ (orderOf u - 1) := by
    calc u⁻¹ = u⁻¹ * u ^ orderOf u := by rw [pow_orderOf_eq_one, mul_one]
      _ = u⁻¹ * (u * u ^ (orderOf u - 1)) := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      _ = u ^ (orderOf u - 1) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hy : y = ((u ^ (orderOf u - 1) : Mˣ) : M) := by rw [← e]; rfl
  rw [hy, Units.val_pow_eq_pow_val]
  exact pow_mem hx _

private noncomputable def chunkRun (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih2 J S => CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (andB (Nat.blt (nat_lit 0) S) (insOK RB mul vld ONE S (bitsN J (nat_lit 0) (nat_lit 50)))))
      (ih2 (Nat.shiftRight J (nat_lit 50))))

private theorem chunkRun_succ (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE m J S : Nat) :
    chunkRun RB mul vld ONE (m + 1) J S =
      CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
          (andB (Nat.blt (nat_lit 0) S) (insOK RB mul vld ONE S (bitsN J (nat_lit 0) (nat_lit 50)))))
        (chunkRun RB mul vld ONE m (Nat.shiftRight J (nat_lit 50))) :=
  rfl

private theorem runSlp_cons (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE C : Nat) (Cs : List Nat) (s : Nat) :
    runSlp RB mul vld ONE (C :: Cs) s =
      runSlp RB mul vld ONE Cs (chunkRun RB mul vld ONE (Nat.land C (nat_lit 255))
        (Nat.shiftRight C (nat_lit 8)) s) :=
  strictN_eq' _ _

theorem slpSeg_sound {d w S T L H CM RM ONE LV HV nb Lg S0 S1 : Nat} {RB : Nat → Nat} {Cs : List Nat}
    (hc : constsOK 2 w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hS : Nat.beq (runSlp RB (mulR 2 w S d T L H CM RM) (validM 2 nb L H) ONE Cs S0) S1 = true)
    (h0 : RegsIn d w S nb L H Lg RB S0) : RegsIn d w S nb L H Lg RB S1 := by
  subst hnb
  set C := Submonoid.closure (rootSet d w S Lg RB) with hC
  have : Finite (Matrix (Fin d) (Fin d) (ZMod 2)) :=
    inferInstanceAs (Finite (Fin d → Fin d → ZMod 2))
  obtain ⟨hONEc, hONE⟩ := one_sound hc
  let Q : Nat → Prop := fun X => Canon 2 d w X ∧ ordMat 2 d w S X ∈ C
  have hmulQ : ∀ A B, Q A → Q B → Q (mulR 2 w S d T L H CM RM A B) := by
    intro A B hA hB
    obtain ⟨h1, h2⟩ := mulR_sound hc hA.1 hB.1
    exact ⟨h1, by rw [h2]; exact C.mul_mem hA.2 hB.2⟩
  have hQ : ∀ r, 0 < r → ∀ s, RegsIn d w S (d * S) L H Lg RB s → r < s → Q (RB r) := by
    intro r hr s hs hrs
    obtain ⟨h1, h2⟩ := hs r hr hrs
    exact ⟨validM_canon hc h1, h2⟩
  have hins : ∀ s ins, RegsIn d w S (d * S) L H Lg RB s → 0 < s →
      insOK RB (mulR 2 w S d T L H CM RM) (validM 2 (d * S) L H) ONE s ins = true →
      RegsIn d w S (d * S) L H Lg RB (s + 1) := by
    intro s ins hs hs0 h
    have hnew : validM 2 (d * S) L H (RB s) = true ∧ ordMat 2 d w S (RB s) ∈ C := by
      unfold insOK at h
      generalize Nat.land ins (nat_lit 3) = k at h
      generalize bitsN ins (nat_lit 2) (nat_lit 16) = a at h
      generalize bitsN ins (nat_lit 18) (nat_lit 16) = b at h
      generalize bitsN ins (nat_lit 34) (nat_lit 16) = e at h
      dsimp only at h
      revert h
      cases Nat.beq k (nat_lit 0)
      · cases Nat.beq k (nat_lit 1)
        · cases Nat.beq k (nat_lit 2)
          · intro h
            exact absurd h Bool.false_ne_true
          · intro h
            obtain ⟨ha, h⟩ := andB_true' h
            obtain ⟨hv, h⟩ := andB_true' h
            obtain ⟨ha0, has⟩ := andB_true' ha
            have hQa := hQ a (Nat.blt_eq.mp ha0) s hs (Nat.blt_eq.mp has)
            have hcs := validM_canon hc hv
            have hm := (mulR_sound hc hQa.1 hcs).2
            rw [Nat.eq_of_beq_eq_true h, hONE] at hm
            have hxy : ordMat 2 d w S (RB a) * ordMat 2 d w S (RB s) = 1 := hm.symm
            exact ⟨hv, inv_mem_of_finite hQa.2 hxy (mul_eq_one_comm.1 hxy)⟩
        · intro h
          obtain ⟨ha, h⟩ := andB_true' h
          obtain ⟨-, h⟩ := andB_true' h
          obtain ⟨ha0, has⟩ := andB_true' ha
          have hQa := hQ a (Nat.blt_eq.mp ha0) s hs (Nat.blt_eq.mp has)
          have hp := powR_pres (Q := Q) e hmulQ ⟨hONEc, by rw [hONE]; exact C.one_mem⟩ hQa
          rw [← Nat.eq_of_beq_eq_true h] at hp
          exact ⟨CFSG.KS.OrdCanon.validM_of_canon hc hp.1, hp.2⟩
      · intro h
        obtain ⟨ha, h⟩ := andB_true' h
        obtain ⟨hb, h⟩ := andB_true' h
        obtain ⟨ha0, has⟩ := andB_true' ha
        obtain ⟨hb0, hbs⟩ := andB_true' hb
        have hQa := hQ a (Nat.blt_eq.mp ha0) s hs (Nat.blt_eq.mp has)
        have hQb := hQ b (Nat.blt_eq.mp hb0) s hs (Nat.blt_eq.mp hbs)
        have hp := hmulQ _ _ hQa hQb
        rw [← Nat.eq_of_beq_eq_true h] at hp
        exact ⟨CFSG.KS.OrdCanon.validM_of_canon hc hp.1, hp.2⟩
    intro r hr hrs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hrs with hrs | rfl
    · exact hs r hr hrs
    · exact hnew
  have hzero : RegsIn d w S (d * S) L H Lg RB 0 := fun r _ hr => absurd hr (Nat.not_lt_zero r)
  have hchunk : ∀ m J s, RegsIn d w S (d * S) L H Lg RB s →
      RegsIn d w S (d * S) L H Lg RB
        (chunkRun RB (mulR 2 w S d T L H CM RM) (validM 2 (d * S) L H) ONE m J s) := by
    intro m
    induction m with
    | zero => intro J s hs; exact hs
    | succ m ih =>
      intro J s hs
      rw [chunkRun_succ, strictN_eq']
      refine ih (Nat.shiftRight J (nat_lit 50)) _ ?_
      cases hb : andB (Nat.blt (nat_lit 0) s)
          (insOK RB (mulR 2 w S d T L H CM RM) (validM 2 (d * S) L H) ONE s
            (bitsN J (nat_lit 0) (nat_lit 50)))
      · exact hzero
      · obtain ⟨h1, h2⟩ := andB_true' hb
        exact hins s _ hs (Nat.blt_eq.mp h1) h2
  have hrun : ∀ (Cs : List Nat) s, RegsIn d w S (d * S) L H Lg RB s →
      RegsIn d w S (d * S) L H Lg RB
        (runSlp RB (mulR 2 w S d T L H CM RM) (validM 2 (d * S) L H) ONE Cs s) := by
    intro Cs
    induction Cs with
    | nil => intro s hs; exact hs
    | cons C Cs ih =>
      intro s hs
      rw [runSlp_cons]
      exact ih _ (hchunk _ _ _ hs)
  rw [← Nat.eq_of_beq_eq_true hS]
  exact hrun Cs S0 h0

theorem regsIn_roots {d w S L H nb Lg : Nat} {RB : Nat → Nat}
    (hroot : rootsOK RB (validM 2 nb L H) 1 (Lg + 1) = true) :
    RegsIn d w S nb L H Lg RB (Lg + 1) := by
  intro r hr0 hr
  refine ⟨?_, Submonoid.subset_closure ⟨r, hr0, by omega, rfl⟩⟩
  have key : ∀ m, m ≤ Lg + 1 → rootsOK RB (validM 2 nb L H) 1 m = true →
      ∀ i, 1 ≤ i → i < m → validM 2 nb L H (RB i) = true := by
    intro m
    induction m with
    | zero => intro _ _ i _ hi; omega
    | succ m ih =>
      intro hm h i hi1 him
      have h' : andB (rootsOK RB (validM 2 nb L H) 1 m)
          (Bool.rec (motive := fun _ => Bool) true (validM 2 nb L H (RB m)) (Nat.ble 1 m)) = true := h
      obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h'
      rcases Nat.lt_or_ge i m with h3 | h3
      · exact ih (by omega) h1 i hi1 h3
      · have : i = m := by omega
        subst this
        have hb : Nat.ble 1 i = true := Nat.ble_eq.mpr hi1
        rw [hb] at h2
        exact h2
  exact key (Lg + 1) le_rfl hroot r hr0 hr

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  simpa [Nat.blt_eq] using h

theorem le_range_of_hom (D : CFSG.Sporadic.SmallF2.Native.VecData) (P : TauCeti.GroupPresentation)
    {w S T L H CM RM ONE LV HV nb Lg Sfin hA hB : Nat} {RB RW : Nat → Nat}
    {rels : List (List (Nat × Bool))}
    (hc : constsOK 2 w S D.d T L H CM RM ONE LV HV = true) (hnb : nb = D.d * S)
    (hrelsP : P.relatorLetters = rels) (hgen : P.generatorCount = Lg)
    (hroot : rootsOK RB (validM 2 nb L H) 1 (Lg + 1) = true)
    (hinv : invsOK RB (mulR 2 w S D.d T L H CM RM) (validM 2 nb L H) Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (hr : ∀ r < lenRels rels, relOK RB (mulR 2 w S D.d T L H CM RM) rels Lg ONE r = true ∨
      ∃ s < r, relDupOK rels s r = true)
    (hregs : RegsIn D.d w S nb L H Lg RB Sfin)
    (hA0 : 0 < hA) (hAS : hA < Sfin) (hB0 : 0 < hB) (hBS : hB < Sfin)
    (hRA : RB hA = RW 1) (hRB : RB hB = RW 2)
    (hmA : mA D = ordMat 2 D.d w S (RW 1)) (hmB : mB D = ordMat 2 D.d w S (RW 2)) :
    ∃ φ : P.Group →* GL (Fin D.d) (ZMod 2), J D ≤ φ.range := by
  obtain ⟨hX, hrel⟩ := rels_sound (hnb := hnb) hc hroot hinv hb hr
  set X : Nat → Matrix (Fin D.d) (Fin D.d) (ZMod 2) := fun r => ordMat 2 D.d w S (RB r) with hXdef
  have hXl : ∀ g < Lg, X (Lg + 1 + g) * X (g + 1) = 1 := fun g hg => mul_eq_one_comm.mp (hX g hg)
  let uX : Nat → GL (Fin D.d) (ZMod 2) := fun g =>
    if hg : g < Lg then ⟨X (g + 1), X (Lg + 1 + g), hX g hg, hXl g hg⟩ else 1
  have huX : ∀ g (hg : g < Lg), (uX g : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = X (g + 1) := by
    intro g hg
    simp [uX, hg]
  have huXi : ∀ g (hg : g < Lg), ((uX g)⁻¹ : GL (Fin D.d) (ZMod 2)).val = X (Lg + 1 + g) := by
    intro g hg
    simp [uX, hg]
  have hletv : ∀ x : Nat × Bool, x.1 < Lg →
      ((if x.2 then uX x.1 else (uX x.1)⁻¹ : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) =
        ordMat 2 D.d w S (letM RB Lg x) := by
    rintro ⟨g, s⟩ hg
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [huXi g hg]
      rfl
    · simp only [↓reduceIte]
      rw [huX g hg]
      rfl
  have hrelP : ∀ v ∈ P.relatorLetters, wordProd uX v = 1 := by
    intro v hv
    rw [hrelsP] at hv
    have hlt := relsBounded_spec hb v hv
    apply Units.ext
    rw [wordProd, Units.val_one, ← hrel v hv, ← Units.coeHom_apply, map_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro x hx
    exact hletv x (hlt x hx)
  have hg : ∀ i < Lg, i < P.generatorCount := fun i hi => hgen ▸ hi
  let φ := presHom P uX hrelP
  have hcl : ∀ M ∈ Submonoid.closure (rootSet D.d w S Lg RB),
      ∃ u ∈ φ.range, (u : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = M := by
    intro M hM
    induction hM using Submonoid.closure_induction with
    | mem M hM =>
      obtain ⟨g, hg0, hg2, rfl⟩ := hM
      rcases Nat.lt_or_ge Lg g with hgl | hgl
      · refine ⟨(uX (g - Lg - 1))⁻¹,
          Subgroup.inv_mem _ ⟨presGen P (g - Lg - 1), presHom_presGen P uX hrelP (hg _ (by omega))⟩, ?_⟩
        rw [huXi _ (by omega)]
        have e : Lg + 1 + (g - Lg - 1) = g := by omega
        rw [e]
      · refine ⟨uX (g - 1), ⟨presGen P (g - 1), presHom_presGen P uX hrelP (hg _ (by omega))⟩, ?_⟩
        rw [huX _ (by omega)]
        have e : g - 1 + 1 = g := by omega
        rw [e]
    | one => exact ⟨1, Subgroup.one_mem _, rfl⟩
    | mul M N _ _ hM hN =>
      obtain ⟨u, hu, rfl⟩ := hM
      obtain ⟨v, hv, rfl⟩ := hN
      exact ⟨u * v, Subgroup.mul_mem _ hu hv, rfl⟩
  have hseed : ∀ (M : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) (r : Nat), 0 < r → r < Sfin →
      M = ordMat 2 D.d w S (RB r) →
      ∀ g : GL (Fin D.d) (ZMod 2),
        g = (if h : M.det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero M h else 1) → g ∈ φ.range := by
    intro M r hr0 hrS hM g hgdef
    obtain ⟨u, hu, hval⟩ := hcl _ (hregs r hr0 hrS).2
    have hdet : M.det ≠ 0 := by
      rw [hM, ← hval]
      exact (Matrix.isUnits_det_units u).ne_zero
    have : g = u := by
      rw [hgdef]
      simp only [ne_eq, hdet, not_false_eq_true, ↓reduceDIte]
      apply Units.ext
      rw [hval, ← hM]
      rfl
    rw [this]
    exact hu
  have hJ : J D ≤ φ.range := by
    rw [J, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hseed (mA D) hA hA0 hAS (by rw [hmA, hRA]) _ rfl
    · exact hseed (mB D) hB hB0 hBS (by rw [hmB, hRB]) _ rfl
  exact ⟨φ, hJ⟩

theorem card_J_le_of_hom (D : CFSG.Sporadic.SmallF2.Native.VecData) (P : TauCeti.GroupPresentation)
    {w S T L H CM RM ONE LV HV nb Lg Sfin hA hB k : Nat} {RB RW : Nat → Nat}
    {rels : List (List (Nat × Bool))}
    (hc : constsOK 2 w S D.d T L H CM RM ONE LV HV = true) (hnb : nb = D.d * S)
    (hrelsP : P.relatorLetters = rels) (hgen : P.generatorCount = Lg)
    (hroot : rootsOK RB (validM 2 nb L H) 1 (Lg + 1) = true)
    (hinv : invsOK RB (mulR 2 w S D.d T L H CM RM) (validM 2 nb L H) Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (hr : ∀ r < lenRels rels, relOK RB (mulR 2 w S D.d T L H CM RM) rels Lg ONE r = true ∨
      ∃ s < r, relDupOK rels s r = true)
    (hregs : RegsIn D.d w S nb L H Lg RB Sfin)
    (hA0 : 0 < hA) (hAS : hA < Sfin) (hB0 : 0 < hB) (hBS : hB < Sfin)
    (hRA : RB hA = RW 1) (hRB : RB hB = RW 2)
    (hmA : mA D = ordMat 2 D.d w S (RW 1)) (hmB : mB D = ordMat 2 D.d w S (RW 2))
    [Finite P.Group] (hcard : Nat.card P.Group ≤ k) : Nat.card (J D) ≤ k := by
  obtain ⟨φ, hJ⟩ := le_range_of_hom D P hc hnb hrelsP hgen hroot hinv hb hr hregs hA0 hAS hB0 hBS
    hRA hRB hmA hmB
  have hfin : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  calc Nat.card (J D) ≤ Nat.card φ.range := Subgroup.card_le_of_le hJ
    _ ≤ Nat.card P.Group := Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
    _ ≤ k := hcard

end CertificateChecks.KernelVec

end
