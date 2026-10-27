
module

public import Certificates.Kernel.Ly3085.Omega.ThreeB
public import Certificates.Kernel.Ly3085.Omega.Base
public import Certificates.Kernel.SporSch.Ly.Seven2189
public import CFSG.Certificates.Kernel.LyOmega.CentSound
public import CFSG.Sporadic.Schreier.LySevenProofBase
public import CFSG.Sporadic.Ly.OmegaCent
public import CFSG.Certificates.Kernel.LyOmega.Sound
public import CFSG.Sporadic.HN.ConjSimple
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.FiveFacts
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.Ly.WordFacts
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm
open CertificateChecks.KernelSporSch

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h (by simp)
  · exact ⟨rfl, h⟩

theorem recAnd {p : ℕ → Bool} : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => Bool.rec (motive := fun _ => Bool) false ih (p t)) n = true → ∀ t < n, p t = true
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | n + 1, h, t, ht => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact recAnd n h2 t ht
    · exact h1

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem fldW_eq (r o w : ℕ) : CFSG.KC.LL.fldW r o w = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem lanes_inj : ∀ (n X Y : ℕ), X < 2 ^ (11 * n) → Y < 2 ^ (11 * n) →
    (∀ q < n, X / 2 ^ (11 * q) % 2 ^ 11 = Y / 2 ^ (11 * q) % 2 ^ 11) → X = Y
  | 0, X, Y, hX, hY, _ => by simp at hX hY; omega
  | n + 1, X, Y, hX, hY, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, pow_zero, Nat.div_one] at h0
    have hdiv : ∀ Z : ℕ, Z < 2 ^ (11 * (n + 1)) → Z / 2 ^ 11 < 2 ^ (11 * n) := by
      intro Z hZ
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      convert hZ using 2
    have hq : ∀ (Z q : ℕ), Z / 2 ^ 11 / 2 ^ (11 * q) = Z / 2 ^ (11 * (q + 1)) := by
      intro Z q
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      congr 2
      ring
    have e := lanes_inj n (X / 2 ^ 11) (Y / 2 ^ 11) (hdiv X hX) (hdiv Y hY) (fun q hq' => by
      rw [hq, hq]
      exact h (q + 1) (by omega))
    rw [← Nat.div_add_mod X (2 ^ 11), ← Nat.div_add_mod Y (2 ^ 11), e, h0]

theorem smM_inj {X Y : ℕ} (hX : LCanon 11 7 7 X) (hY : LCanon 11 7 7 Y) (h : smM X = smM Y) :
    X = Y := by
  have hb : (11 * 7 * 7 : ℕ) = 11 * 49 := by norm_num
  refine lanes_inj 49 X Y (hb ▸ hX.1) (hb ▸ hY.1) fun q hq => ?_
  have hi : q / 7 < 7 := by omega
  have hj : q % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have ho : 11 * 7 * (q / 7) + 11 * (q % 7) = 11 * q := by omega
  have hfX := hX.2 _ hi _ hj
  have hfY := hY.2 _ hi _ hj
  rw [ho] at hfX hfY
  have e := congrFun (congrFun h ⟨q / 7, hi⟩) ⟨q % 7, hj⟩
  simp only [smM, ent] at e
  have ho' : 77 * (q / 7) + 11 * (q % 7) = 11 * q := by omega
  rw [ho', ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hfX, Nat.mod_eq_of_lt hfY] at e
  exact e

theorem smM_eq_mat7 {X : ℕ} {ra : Array ℕ}
    (h : ∀ t < 49, Nat.beq (CFSG.KC.LyOm.sEnt X (Nat.div t 7) (Nat.mod t 7)) (ra[t]!) = true) :
    smM X = mat7 ra := by
  ext a b
  have e := Nat.eq_of_beq_eq_true (h (7 * a.val + b.val) (by omega))
  have h1 : Nat.div (7 * a.val + b.val) 7 = a.val := by
    change (7 * a.val + b.val) / 7 = a.val
    omega
  have h2 : Nat.mod (7 * a.val + b.val) 7 = b.val := by
    change (7 * a.val + b.val) % 7 = b.val
    omega
  rw [h1, h2] at e
  unfold CFSG.KC.LyOm.sEnt at e
  rw [fldW_eq] at e
  simp only [smM, ent, mat7, Matrix.of_apply]
  rw [← e]
  rfl

theorem hSC : CFSG.KC.LyOm.sConstsOK CFSG.KD.LyOm.SC = true := by
  have h := CFSG.KD.LyOm.consts
  generalize CFSG.KD.LyOm.BC = b at h
  generalize hs : CFSG.KD.LyOm.SC = s at h
  subst hs
  exact (bAnd_true h).2

theorem one_fields : ∀ i j : Fin 7,
    CFSG.KD.LyOm.SC.ONE / 2 ^ (77 * i.val + 11 * j.val) % 2 ^ 11 = if i = j then 1 else 0 := by
  decide +kernel

theorem smM_one : smM CFSG.KD.LyOm.SC.ONE = 1 := by
  ext i j
  simp only [smM, ent, Matrix.one_apply]
  rw [one_fields i j]
  split_ifs <;> simp

theorem canon_one : LCanon 11 7 7 CFSG.KD.LyOm.SC.ONE := by
  unfold LCanon
  decide +kernel

theorem rOK_facts {R Q KQ KR : ℕ} {ra : Array ℕ} (h : CFSG.KD.LyOm.rOK R Q KQ KR ra = true) :
    LCanon 11 7 7 R ∧ LCanon 11 7 7 Q ∧ smM R = mat7 ra ∧ smM R * smM Q = 1 := by
  unfold CFSG.KD.LyOm.rOK at h
  obtain ⟨hR, h⟩ := bAnd_true h
  obtain ⟨hQ, h⟩ := bAnd_true h
  obtain ⟨he, h⟩ := bAnd_true h
  obtain ⟨hRQ, -⟩ := bAnd_true h
  have cR := sVld_sound hSC hR
  have cQ := sVld_sound hSC hQ
  refine ⟨cR, cQ, smM_eq_mat7 (recAnd 49 he), ?_⟩
  rw [← (sMul_sound hSC cR cQ).2, Nat.eq_of_beq_eq_true hRQ, smM_one]

theorem genArr_eq (j : ℕ) (hj : j < 5) : genArr j = LySv.RA[j]! := by
  unfold genArr asArr
  rw [LyBSF.b4_eq]
  exact LySvF.gensA j hj

theorem restr7_mul [LySeed] {g h : J}
    (hg : g ∈ stabU) (hh : h ∈ stabU) : restr7 (g * h) = restr7 g * restr7 h :=
  restr7_of_eq (stabU_mul hg hh)

theorem restr7_inv [LySeed] {g : J}
    (hg : g ∈ stabU) : restr7 g⁻¹ = (restr7 g)⁻¹ := by
  have := rho7_inv ⟨g, hg⟩
  rw [rho7_apply, rho7_apply] at this
  exact this

theorem restr7_mul_inv [LySeed] {g : J}
    (hg : g ∈ stabU) : restr7 g * restr7 g⁻¹ = 1 := by
  rw [← restr7_mul hg (stabU.inv_mem hg), mul_inv_cancel, restr7_one]

theorem gen_facts
    [LySeed] {R Q KQ KR j : ℕ} (hj : j < 2)
    (h : CFSG.KD.LyOm.rOK R Q KQ KR (LySv.RA[j]!) = true) :
    LCanon 11 7 7 R ∧ LCanon 11 7 7 Q ∧ smM R = restr7 (aStar (j + 2)) ∧
      smM Q = restr7 (aStar (j + 2))⁻¹ := by
  obtain ⟨cR, cQ, eR, eRQ⟩ := rOK_facts h
  have hS := aStar_mem_stabU (j := j + 2) (by omega) (by omega)
  have eR' : smM R = restr7 (aStar (j + 2)) := by
    rw [eR, ← genArr_eq j (by omega), mat7_genArr]
  refine ⟨cR, cQ, eR', ?_⟩
  rw [restr7_inv hS, ← eR']
  exact (Matrix.inv_eq_right_inv eRQ).symm

theorem lyLet_mem [LySeed] (l : ℕ) : lyLet l ∈ lyH := by
  have h2 := aStar_mem_lyH (j := 2) le_rfl
  have h3 := aStar_mem_lyH (j := 3) (by norm_num)
  unfold lyLet
  rcases l with _ | _ | _ | _ | l
  · exact h2
  · exact h3
  · exact lyH.inv_mem h2
  · exact lyH.inv_mem h3
  · exact lyH.one_mem

theorem wordJ_mem [LySeed] (w : List ℕ) : wordJ w ∈ lyH := by
  unfold wordJ
  induction w with
  | nil => exact lyH.one_mem
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    exact lyH.mul_mem (lyLet_mem l) ih

theorem gr_facts
    [LySeed] {l : ℕ} (hl : l < 4) :
    LCanon 11 7 7 (CFSG.KD.LyY.GR l) ∧ smM (CFSG.KD.LyY.GR l) = restr7 (lyLet l) := by
  obtain ⟨c0, d0, e0, f0⟩ := gen_facts (j := 0) (by norm_num) CFSG.KD.LyOm.r0
  obtain ⟨c1, d1, e1, f1⟩ := gen_facts (j := 1) (by norm_num) CFSG.KD.LyOm.r1
  interval_cases l
  · exact ⟨c0, e0⟩
  · exact ⟨c1, e1⟩
  · exact ⟨d0, f0⟩
  · exact ⟨d1, f1⟩

theorem sWord_spec
    [LySeed] : ∀ (w : List ℕ) (X : ℕ), (∀ l ∈ w, l < 4) → LCanon 11 7 7 X →
    LCanon 11 7 7 (CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR X w) ∧
      smM (CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR X w) = smM X * restr7 (wordJ w)
  | [], X, _, hX => ⟨hX, by
      change smM X = smM X * restr7 ((([] : List ℕ).map lyLet).prod)
      rw [List.map_nil, List.prod_nil, restr7_one, mul_one]⟩
  | l :: w, X, hw, hX => by
    have hl := gr_facts (hw l List.mem_cons_self)
    have hm := sMul_sound hSC hX hl.1
    have e : CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR X (l :: w) =
        CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR
          (CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC X (CFSG.KD.LyY.GR l)) w :=
      strictN_eq' _ _
    obtain ⟨c, s⟩ := sWord_spec w _ (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) hm.1
    refine ⟨e ▸ c, ?_⟩
    rw [e, s, hm.2, hl.2, mul_assoc, ← restr7_mul (lyH_le_stabU (lyLet_mem l))
      (lyH_le_stabU (wordJ_mem w))]
    rfl

theorem restr7_wordJ
    [LySeed] {w : List ℕ} (hw : ∀ l ∈ w, l < 4) :
    LCanon 11 7 7 (CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR CFSG.KD.LyOm.SC.ONE w) ∧
      smM (CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR CFSG.KD.LyOm.SC.ONE w) =
        restr7 (wordJ w) := by
  obtain ⟨c, s⟩ := sWord_spec w _ hw canon_one
  rw [smM_one, one_mul] at s
  exact ⟨c, s⟩

theorem restr7_injOn
    [LySeed] (hH : Nat.card lyH ≤ 5859000000) :
    ∀ h ∈ lyH, restr7 h = 1 → h = 1 := by
  let ψ : lyH' →* lyK := (rhoP.comp lyH'.subtype).codRestrict lyK (fun x => ⟨x, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hH' : Nat.card lyH' = Nat.card lyH :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe lyH_le_stabU).toEquiv
  have hK := card_image_ge
  have hψb : Function.Bijective ψ := hψ.bijective_of_nat_card_le (by rw [hH']; omega)
  intro h hh h1
  have e : ψ ⟨⟨h, lyH_le_stabU hh⟩, Subgroup.mem_subgroupOf.2 hh⟩ = ψ 1 := by
    apply Subtype.ext
    change rhoP ⟨h, lyH_le_stabU hh⟩ = rhoP 1
    rw [map_one]
    exact rhoP_eq_one h1
  have := congrArg (fun x : lyH' => ((x : stabU) : J)) (hψb.1 e)
  simpa using this

theorem restr7_inj
    [LySeed] (hH : Nat.card lyH ≤ 5859000000) {g h : J} (hg : g ∈ lyH)
    (hh : h ∈ lyH) (e : restr7 g = restr7 h) : g = h := by
  have hgs := lyH_le_stabU hg
  have hhs := lyH_le_stabU hh
  have h1 : restr7 (g * h⁻¹) = 1 := by
    rw [restr7_mul hgs (stabU.inv_mem hhs), e, restr7_mul_inv hhs]
  exact mul_inv_eq_one.1 (restr7_injOn hH _ (lyH.mul_mem hg (lyH.inv_mem hh)) h1)

theorem card_centralizer_t_le
    [LySeed] (hH : Nat.card lyH ≤ 5859000000) (ht : lyt ∈ lyH) :
    Nat.card (Subgroup.centralizer ({⟨lyt, ht⟩} : Set lyH)) ≤ 14400 :=
  card_centralizer_le_of_orbit _ (card_conj_class_ge ht) (by omega)

theorem wyb_eq : CFSG.KD.LyOm.WYB = (List.replicate 10 [1, 1, 2, 0, 1, 0, 3, 2, 1, 0]).flatten := by
  decide +kernel

theorem lyYB_eq [LySeed] : lyYB = wordJ CFSG.KD.LyOm.WYB := by
  rw [wyb_eq]
  rfl

@[expose] def lyC0 [LySeed] : J := wordJ CFSG.KD.LyY.WCt

@[expose] def lyGS [LySeed] (s : ℕ) : J :=
  wordJ ([CFSG.KD.LyY.WS0, CFSG.KD.LyY.WS1, CFSG.KD.LyY.WS2].getD s [])

theorem wyb_lt : ∀ l ∈ CFSG.KD.LyOm.WYB, l < 4 := by decide +kernel
theorem wct_lt : ∀ l ∈ CFSG.KD.LyY.WCt, l < 4 := by decide +kernel
theorem ws0_lt : ∀ l ∈ CFSG.KD.LyY.WS0, l < 4 := by decide +kernel
theorem ws1_lt : ∀ l ∈ CFSG.KD.LyY.WS1, l < 4 := by decide +kernel
theorem ws2_lt : ∀ l ∈ CFSG.KD.LyY.WS2, l < 4 := by decide +kernel

theorem gs0 : CFSG.KD.LyY.GS 0 =
    CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR CFSG.KD.LyOm.SC.ONE CFSG.KD.LyY.WS0 := by
  unfold CFSG.KD.LyY.GS CFSG.KC.LL.pickL
  rfl

theorem gs1 : CFSG.KD.LyY.GS 1 =
    CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR CFSG.KD.LyOm.SC.ONE CFSG.KD.LyY.WS1 := by
  unfold CFSG.KD.LyY.GS CFSG.KC.LL.pickL
  rfl

theorem gs2 : CFSG.KD.LyY.GS 2 =
    CFSG.KC.LyOm.sWord CFSG.KD.LyOm.SC CFSG.KD.LyY.GR CFSG.KD.LyOm.SC.ONE CFSG.KD.LyY.WS2 := by
  unfold CFSG.KD.LyY.GS CFSG.KC.LL.pickL
  rfl

theorem gs_facts
    [LySeed] {s : ℕ} (hs : s < 3) :
    LCanon 11 7 7 (CFSG.KD.LyY.GS s) ∧ smM (CFSG.KD.LyY.GS s) = restr7 (lyGS s) := by
  interval_cases s
  · rw [gs0]
    exact restr7_wordJ ws0_lt
  · rw [gs1]
    exact restr7_wordJ ws1_lt
  · rw [gs2]
    exact restr7_wordJ ws2_lt

theorem card_centralizer_yB_le
    [LySeed] (hH : Nat.card lyH ≤ 5859000000) (ht : lyt ∈ lyH) :
    Nat.card (Subgroup.centralizer ({⟨lyYB, wordJ_mem _⟩} : Set lyH)) ≤ 720 := by
  have hts := lyH_le_stabU ht
  have hcH : lyC0 ∈ lyH := wordJ_mem _
  have hcs := lyH_le_stabU hcH
  have cY : LCanon 11 7 7 CFSG.KD.LyY.Y := (restr7_wordJ wyb_lt).1
  have eY : smM CFSG.KD.LyY.Y = restr7 lyYB := by rw [lyYB_eq]; exact (restr7_wordJ wyb_lt).2
  have cC : LCanon 11 7 7 CFSG.KD.LyY.GC := (restr7_wordJ wct_lt).1
  have eC : smM CFSG.KD.LyY.GC = restr7 lyC0 := (restr7_wordJ wct_lt).2
  have hquad := CFSG.KD.LyY.quad
  generalize hT : CFSG.KD.LyY.T0 = T at hquad
  generalize hYv : CFSG.KD.LyY.Y = Yv at hquad
  obtain ⟨hT0, hq⟩ := bAnd_true hquad
  subst hT hYv
  have cT0 := sVld_sound hSC hT0
  have eT0 : smM CFSG.KD.LyY.T0 = ((4 : ℕ) : ZMod 5) • smM CFSG.KD.LyY.Y ^ 2 +
      ((4 : ℕ) : ZMod 5) • smM CFSG.KD.LyY.Y + ((3 : ℕ) : ZMod 5) • 1 := by
    rw [← Nat.eq_of_beq_eq_true hq]
    exact (sQuad_sound hSC (by norm_num) (by norm_num) (by norm_num) cY).2
  have hrt := CFSG.KD.LyOm.clsRT
  generalize hR : CFSG.KD.LyOm.RTl = Rv at hrt
  obtain ⟨hR1, hrt⟩ := bAnd_true hrt
  obtain ⟨hR2, -⟩ := bAnd_true hrt
  subst hR
  have cRT : LCanon 11 7 7 CFSG.KD.LyOm.RTl := sVld_sound hSC hR1
  have eRT : smM CFSG.KD.LyOm.RTl = restr7 lyt := by
    rw [smM_eq_mat7 (ra := LySv.RT) (recAnd (p := fun t => Nat.beq (CFSG.KC.LyOm.sEnt
      CFSG.KD.LyOm.RTl (Nat.div t 7) (Nat.mod t 7)) (LySv.RT[t]!)) 49 hR2), ← LySvF.rt_eq, ← LySvF.v_eq, ← LyBSF.b4_eq]
    exact mat7_restrArr repM_tArr
  let t0 : J := lyC0 * lyt * lyC0⁻¹
  have ht0 : t0 ∈ lyH := lyH.mul_mem (lyH.mul_mem hcH ht) (lyH.inv_mem hcH)
  have econj : smM CFSG.KD.LyY.GC * smM CFSG.KD.LyOm.RTl =
      smM CFSG.KD.LyY.T0 * smM CFSG.KD.LyY.GC := by
    rw [← (sMul_sound hSC cC cRT).2, ← (sMul_sound hSC cT0 cC).2,
      Nat.eq_of_beq_eq_true CFSG.KD.LyY.conj]
  have e0 : smM CFSG.KD.LyY.T0 = restr7 t0 := by
    have hinv := restr7_mul_inv hcs
    have e1 : restr7 lyC0 * restr7 lyt = smM CFSG.KD.LyY.T0 * restr7 lyC0 := by
      rw [← eC, ← eRT]
      exact econj
    calc smM CFSG.KD.LyY.T0 = smM CFSG.KD.LyY.T0 * restr7 lyC0 * restr7 lyC0⁻¹ := by
          rw [mul_assoc, hinv, mul_one]
      _ = restr7 lyC0 * restr7 lyt * restr7 lyC0⁻¹ := by rw [e1]
      _ = restr7 t0 := by
          rw [restr7_mul (stabU.mul_mem hcs hts) (stabU.inv_mem hcs), restr7_mul hcs hts]
  have hpoly : ∀ M : Matrix (Fin 7) (Fin 7) (ZMod 5), Commute M (restr7 lyYB) →
      Commute M (restr7 t0) := by
    intro M hM
    rw [← e0, eT0]
    rw [← eY] at hM
    exact (((hM.pow_right 2).smul_right _).add_right (hM.smul_right _)).add_right
      ((Commute.one_right M).smul_right _)
  have hcomm : ∀ {g h : J}, g ∈ lyH → h ∈ lyH → Commute (restr7 g) (restr7 h) → Commute g h := by
    intro g h hg hh e
    apply restr7_inj hH (lyH.mul_mem hg hh) (lyH.mul_mem hh hg)
    rw [restr7_mul (lyH_le_stabU hg) (lyH_le_stabU hh), restr7_mul (lyH_le_stabU hh) (lyH_le_stabU hg)]
    exact e.eq
  have hgs : ∀ s < 3, Commute (lyGS s) t0 := by
    intro s hs
    obtain ⟨cG, eG⟩ := gs_facts hs
    apply hcomm (wordJ_mem _) ht0
    change Commute (restr7 (lyGS s)) (restr7 t0)
    rw [← eG, ← e0]
    have hc := CFSG.KD.LyY.cent
    generalize hT : CFSG.KD.LyY.T0 = T at hc
    generalize hG : CFSG.KD.LyY.GS = G at hc
    obtain ⟨h0, h12⟩ := bAnd_true hc
    obtain ⟨h1, h2⟩ := bAnd_true h12
    subst hT hG
    have key : CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC (CFSG.KD.LyY.GS s) CFSG.KD.LyY.T0 =
        CFSG.KC.LyOm.sMul CFSG.KD.LyOm.SC CFSG.KD.LyY.T0 (CFSG.KD.LyY.GS s) := by
      interval_cases s
      · exact Nat.eq_of_beq_eq_true h0
      · exact Nat.eq_of_beq_eq_true h1
      · exact Nat.eq_of_beq_eq_true h2
    change smM _ * smM _ = smM _ * smM _
    rw [← (sMul_sound hSC cG cT0).2, ← (sMul_sound hSC cT0 cG).2, key]
  obtain ⟨hroot, hcan, hstep, hdist⟩ :=
    sConjTree_sound hSC (fun s hs => (gs_facts hs).1) CFSG.KD.LyY.tree
  have hw : ∀ k < 20, ∃ h : J, h ∈ lyH ∧ Commute h t0 ∧
      smM (CFSG.KC.LL.pickL CFSG.KD.LyY.ZK k) = restr7 (h * lyYB * h⁻¹) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · refine ⟨1, lyH.one_mem, Commute.one_left _, ?_⟩
        simp only [one_mul, inv_one, mul_one]
        rw [← eY]
        exact congrArg smM hroot
      · obtain ⟨hp, hl, he⟩ := hstep k hpos hk
        obtain ⟨h, hH', hc, hm⟩ := ih _ hp (by omega)
        set s := CFSG.KC.LL.pickL CFSG.KD.LyY.ZL k
        obtain ⟨cG, eG⟩ := gs_facts hl
        have hGs : lyGS s ∈ lyH := wordJ_mem _
        refine ⟨lyGS s * h, lyH.mul_mem hGs hH', (hgs s hl).mul_left hc, ?_⟩
        have hGss := lyH_le_stabU hGs
        have hhs := lyH_le_stabU hH'
        have hyb : lyYB ∈ stabU := lyH_le_stabU (wordJ_mem CFSG.KD.LyOm.WYB)
        have hinv := restr7_mul_inv hGss
        have e1 : smM (CFSG.KC.LL.pickL CFSG.KD.LyY.ZK k) * restr7 (lyGS s) =
            restr7 (lyGS s) * restr7 (h * lyYB * h⁻¹) := by
          rw [← eG, ← hm]
          exact he.symm
        calc smM (CFSG.KC.LL.pickL CFSG.KD.LyY.ZK k)
            = smM (CFSG.KC.LL.pickL CFSG.KD.LyY.ZK k) * restr7 (lyGS s) * restr7 (lyGS s)⁻¹ := by
              rw [mul_assoc, hinv, mul_one]
          _ = restr7 (lyGS s) * restr7 (h * lyYB * h⁻¹) * restr7 (lyGS s)⁻¹ := by rw [e1]
          _ = restr7 (lyGS s * h * lyYB * (lyGS s * h)⁻¹) := by
              have hx := stabU.mul_mem (stabU.mul_mem hhs hyb) (stabU.inv_mem hhs)
              have eq1 : lyGS s * h * lyYB * (lyGS s * h)⁻¹ =
                  lyGS s * (h * lyYB * h⁻¹) * (lyGS s)⁻¹ := by group
              rw [eq1, restr7_mul (stabU.mul_mem hGss hx) (stabU.inv_mem hGss), restr7_mul hGss hx]
  choose! hh hhH hhc hhm using hw
  have hyH : lyYB ∈ lyH := wordJ_mem _
  have hyb := lyH_le_stabU hyH
  let f : Fin 20 → lyH := fun k => ⟨hh k * lyYB * (hh k)⁻¹,
    lyH.mul_mem (lyH.mul_mem (hhH k k.2) hyH) (lyH.inv_mem (hhH k k.2))⟩
  have hf : Function.Injective f := by
    intro i j hij
    have e1 := congrArg (fun z : lyH => restr7 (z : J)) hij
    simp only [f] at e1
    rw [← hhm i i.2, ← hhm j j.2] at e1
    exact Fin.ext (hdist i i.2 j j.2 (smM_inj (hcan i i.2) (hcan j j.2) e1))
  have hS := card_mul_card_centralizer_le (G := lyH) ⟨lyYB, hyH⟩ ⟨t0, ht0⟩ ?_ (Set.range f) ?_
  · simp only [Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin] at hS
    have hconj : (⟨t0, ht0⟩ : lyH) = ⟨lyC0, hcH⟩ * ⟨lyt, ht⟩ * (⟨lyC0, hcH⟩ : lyH)⁻¹ := rfl
    rw [hconj, card_centralizer_conj] at hS
    have := card_centralizer_t_le hH ht
    omega
  · intro h hc
    have hc' : ((h * ⟨lyYB, hyH⟩ : lyH) : J) = ((⟨lyYB, hyH⟩ * h : lyH) : J) :=
      congrArg Subtype.val hc.eq
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at hc'
    have hs := lyH_le_stabU h.2
    have m : Commute (restr7 (h : J)) (restr7 lyYB) := by
      unfold Commute SemiconjBy
      rw [← restr7_mul hs hyb, ← restr7_mul hyb hs]
      exact congrArg restr7 hc'
    exact Subtype.ext (hcomm h.2 ht0 (hpoly _ m)).eq
  · rintro z ⟨k, rfl⟩
    exact ⟨⟨hh k, hhH k k.2⟩, Subtype.ext (hhc k k.2).eq, rfl⟩

end CertificateChecks.KernelLy.Omega

end
