
module

public import Certificates.Kernel.GammaU.NormOK
public import Certificates.Kernel.GammaU.Pair
public import CFSG.Certificates.Kernel.GammaUNormSound
public import CFSG.GF2Type.Smith1979.GammaU.StepA2Base

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUNB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem map_conj_mul (a b : GL) (N : Subgroup GL) :
    (N.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      N.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  exact congrArg (fun f => Subgroup.map f N) (MonoidHom.ext fun x => by simp [mul_assoc])

theorem rowsSet_iff {c : Nat} (hc : c < 32) {L : List Nat} (hL : L = five CFSG.KD.GUC0.CG c)
    (l : GL) : RowsSet (compOf c) l ↔ FrP L l := by
  subst hL
  obtain ⟨h1, h2⟩ := CFSG.KD.GUTB.compOf_iff hc
  constructor
  · rintro ⟨r, hr, hlr⟩
    obtain ⟨m, hm, hmv⟩ := h2 r hr
    exact ⟨m, hm, fun v => by rw [hlr, hmv]⟩
  · rintro ⟨m, -, hlm⟩
    obtain ⟨x, hx, hxv⟩ := h1 m
    exact ⟨x, hx, fun v => by rw [hlm, hxv]⟩

theorem nl_of {G Gi : Nat} {F : Nat → Nat} {L : List Nat} {TH : Nat} {D0 : List Nat}
    {nm : Nat → Nat → Nat} (hTH : ∀ v, linP TH v = theta0 v) (hD : ∀ v ∈ D0, v < 4096)
    (hinv : invOK G Gi 3 = true) (hF : ∀ g < 3, F (2 * g) = look G g ∧ F (2 * g + 1) = look Gi g)
    (hnl : ∀ e < 6, nlP L TH D0 (spanList D0) (F e) (nm e) = true) :
    ∀ U ∈ lGrp G 3, NLK L D0 U :=
  lGrp_ind _ (NLK.one _ _) (fun _ _ => NLK.mul) fun g hg U hU => by
    have hUi : IsP U⁻¹ (look Gi g) := hU.inv (invOK_spec _ _ hinv g hg)
    have hA := hnl (2 * g) (by omega)
    have hB := hnl (2 * g + 1) (by omega)
    rw [(hF g hg).1] at hA
    rw [(hF g hg).2] at hB
    refine ⟨nlP_spec hTH hD hA hB hU hUi, nlP_spec hTH hD hB hA hUi ?_⟩
    rw [inv_inv]
    exact hU

@[expose] def ResP (N : Subgroup GL) (RC : List Nat) (U : GL) : Prop :=
  ∀ c < 30, ∃ c' < 30, ∀ A A' : GL, IsP A (nthD 0 RC c) → IsP A' (nthD 0 RC c') →
    N.map (MulAut.conj (U * A)).toMonoidHom = N.map (MulAut.conj A').toMonoidHom

theorem resP_letter {N2 : List Nat} {NN : Nat} {RC RCI : List Nat} {f : Nat} {rec : Nat → List (List Nat)}
    (h : allBelow 30 (fun c => rpOK N2 NN RC RCI f c (rec c)) = true) (hlen : lenN RC = 30)
    (hRC : ∀ c < 30, mulP (nthD 0 RC c) (nthD 0 RCI c) = idP) {N : Subgroup GL}
    (hN : ∀ q < NN, ∃ V ∈ N, IsP V (nthD 0 N2 q))
    (hNle : ∀ M : Subgroup GL, (∀ q < NN, ∀ V, IsP V (nthD 0 N2 q) → V ∈ M) → N ≤ M) {V : GL}
    (hV : IsP V f) : ResP N RC V := by
  intro c hc
  have hr := (allBelow_iff _ _).1 h c hc
  unfold rpOK at hr
  rw [Bool.and_eq_true, Nat.blt_eq, hlen] at hr
  obtain ⟨hc', hat⟩ := hr
  refine ⟨_, hc', fun A A' hA hA' => ?_⟩
  have hA'i := hA'.inv (hRC _ hc')
  have hU := rpAt_spec hat hN hNle (hA'i.mul (hV.mul hA))
  rw [show V * A = A' * (A'⁻¹ * (V * A)) by group, ← map_conj_mul, hU]

theorem resP_mul {N : Subgroup GL} {RC RCI : List Nat}
    (hRC : ∀ c < 30, mulP (nthD 0 RC c) (nthD 0 RCI c) = idP) {x y : GL} (hx : ResP N RC x)
    (hy : ResP N RC y) : ResP N RC (x * y) := by
  intro c hc
  obtain ⟨c₁, hc₁, hy'⟩ := hy c hc
  obtain ⟨c₂, hc₂, hx'⟩ := hx c₁ hc₁
  obtain ⟨A₁, hA₁⟩ := IsP.exists_of_mul (hRC c₁ hc₁)
  refine ⟨c₂, hc₂, fun A A' hA hA' => ?_⟩
  rw [mul_assoc, ← map_conj_mul, hy' A A₁ hA hA₁, map_conj_mul, hx' A₁ A' hA₁ hA']

theorem resP_one (N : Subgroup GL) (RC : List Nat) : ResP N RC 1 := fun c hc =>
  ⟨c, hc, fun A A' hA hA' => by rw [one_mul, IsP.inj hA hA']⟩

end CFSG.KD.GUNB

namespace CFSG.KD.GUN0

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KD.GUNB
open CFSG.KD.GUT0 (L NLG NLGI N2 NN ct16966a_inv)
open CFSG.KD.GUP0 (PM RC RCI)
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem letN_spec {g : Nat} (_ : g < 3) : letN (2 * g) = look NLG g ∧ letN (2 * g + 1) = look NLGI g := by
  unfold letN
  have h0 : Nat.beq (Nat.mod (2 * g) 2) 0 = true := by
    rw [Nat.beq_eq]
    change 2 * g % 2 = 0
    omega
  have h1 : Nat.beq (Nat.mod (2 * g + 1) 2) 0 = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
    change ¬ (2 * g + 1) % 2 = 0
    omega
  have d0 : Nat.div (2 * g) 2 = g := by
    change 2 * g / 2 = g
    omega
  have d1 : Nat.div (2 * g + 1) 2 = g := by
    change (2 * g + 1) / 2 = g
    omega
  rw [h0, h1, cond_true, cond_false, d0, d1]
  exact ⟨rfl, rfl⟩

theorem nl_all {e : Nat} (he : e < 6) : nl e = true := by
  interval_cases e
  exacts [cn16966anl0, cn16966anl1, cn16966anl2, cn16966anl3, cn16966anl4, cn16966anl5]

theorem cv_all {p : Nat} (hp : p < 15) : cv p = true := by
  interval_cases p
  exacts [cn16966acv0, cn16966acv1, cn16966acv2, cn16966acv3, cn16966acv4, cn16966acv5,
    cn16966acv6, cn16966acv7, cn16966acv8, cn16966acv9, cn16966acv10, cn16966acv11,
    cn16966acv12, cn16966acv13, cn16966acv14]

theorem rp_all {e : Nat} (he : e < 6) : rp e = true := by
  interval_cases e
  exacts [cn16966arp0, cn16966arp1, cn16966arp2, cn16966arp3, cn16966arp4, cn16966arp5]

theorem lists_spec : UQ.length = 15 ∧ (∀ m ∈ UQ, m < 32) ∧
    (∀ m < 32, unitP CFSG.KD.GUC0.TH (subQ L m) = true → m = 0 ∨ m ∈ UQ) ∧ lenN RC = 30 ∧
    ∀ c < 30, mulP (nthD 0 RC c) (nthD 0 RCI c) = idP := by
  have h := cn16966a_lists
  unfold lists at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, ltAll_iff, allBelow_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun m hm hu => ?_, by rw [lenN_eq]; exact h4, h5⟩
  have := h3 m hm
  simp only [Bool.or_eq_true, Bool.not_eq_true', hu, Nat.beq_eq, memN_iff] at this
  rcases this with (h | h) | h
  · exact absurd h (by simp)
  · exact Or.inl h
  · exact Or.inr h

theorem d0K_lt : ∀ v ∈ D0K, v < 4096 := by decide

theorem nlk : ∀ U ∈ lGrp NLG 3, NLK L D0K U :=
  nl_of CFSG.KD.GUTB.linP_TH d0K_lt ct16966a_inv (fun _ hg => letN_spec hg) fun _ he => nl_all he

theorem nl_mem {U : GL} (hU : U ∈ lGrp NLG 3) :
    U ∈ gammaU ∧ U (vecOf a0) = vecOf a0 ∧ (∀ y, U y ∈ spanOf d0 ↔ y ∈ spanOf d0) ∧
      ∀ l, RowsSet (compOf 0) (U * l * U⁻¹) ↔ RowsSet (compOf 0) l := by
  obtain ⟨h1, h2, h3, h4⟩ := nlk U hU
  have hd : D0K = d0 := rfl
  rw [hd] at h3
  refine ⟨h1, h2, h3, fun l => ?_⟩
  rw [rowsSet_iff (by norm_num) rfl, rowsSet_iff (by norm_num) rfl]
  exact h4 l

theorem cover {a b : Nat} (ha : a < 32) (hb : b < 32) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b)
    (hua : unitP CFSG.KD.GUC0.TH (subQ L a) = true) (hub : unitP CFSG.KD.GUC0.TH (subQ L b) = true) :
    ∃ k < 2, ∃ U ∈ lGrp NLG 3,
      (∀ v, linP (subQ L a) (U v) = U (linP (subQ L (nthD 0 PM (2 * k))) v)) ∧
        ∀ v, linP (subQ L b) (U v) = U (linP (subQ L (nthD 0 PM (2 * k + 1))) v) := by
  obtain ⟨hlen, -, hcov, -, -⟩ := lists_spec
  have hpos : ∀ m < 32, m ≠ 0 → unitP CFSG.KD.GUC0.TH (subQ L m) = true →
      ∃ p < 15, nthD 0 UQ p = m := by
    intro m hm hm0 hu
    rcases hcov m hm hu with h | h
    · exact absurd h hm0
    · obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem h
      exact ⟨p, by rw [← hlen]; exact hp, by rw [nthD_eq, getD_of_lt _ hp]⟩
  obtain ⟨p, hp, rfl⟩ := hpos a ha ha0 hua
  obtain ⟨q, hq, rfl⟩ := hpos b hb hb0 hub
  have hpq : p ≠ q := fun h => hab (by rw [h])
  have hrow := (allBelow_iff _ _).1 (cv_all hp) q hq
  have hbeq : Nat.beq p q = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
    exact hpq
  rw [hbeq, Bool.false_or] at hrow
  unfold cvOK at hrow
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at hrow
  obtain ⟨⟨hk, hw⟩, hat⟩ := hrow
  obtain ⟨U, hUm, hUP⟩ := CFSG.KD.GUTB.isP_wordP ct16966a_inv _ hw
  exact ⟨_, hk, U, hUm, cvAt_spec hat hUP⟩

theorem res_perm : ∀ U ∈ lGrp NLG 3, ResP (ResPair.n2 0) RC U := by
  obtain ⟨-, -, -, hlen, hRC⟩ := lists_spec
  have hlet : ∀ e < 6, ∀ V, IsP V (letN e) → ResP (ResPair.n2 0) RC V := fun e he V hV =>
    resP_letter (rp_all he) hlen hRC CFSG.KD.GUP0.n2_mem (fun M hM => CFSG.KD.GUP0.n2_le' hM) hV
  refine lGrp_ind _ (resP_one _ _) (fun _ _ => resP_mul hRC) fun g hg U hU => ?_
  have hUi : IsP U⁻¹ (look NLGI g) := hU.inv (invOK_spec _ _ ct16966a_inv g hg)
  obtain ⟨h0, h1⟩ := letN_spec hg
  exact ⟨hlet (2 * g) (by omega) U (by rw [h0]; exact hU),
    hlet (2 * g + 1) (by omega) U⁻¹ (by rw [h1]; exact hUi)⟩

end CFSG.KD.GUN0

namespace CFSG.KD.GUN1

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KD.GUNB
open CFSG.KD.GUT1 (L NLG NLGI N2 NN ct16966b_inv)
open CFSG.KD.GUP1 (PM RC RCI)
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem letN_spec {g : Nat} (_ : g < 3) : letN (2 * g) = look NLG g ∧ letN (2 * g + 1) = look NLGI g := by
  unfold letN
  have h0 : Nat.beq (Nat.mod (2 * g) 2) 0 = true := by
    rw [Nat.beq_eq]
    change 2 * g % 2 = 0
    omega
  have h1 : Nat.beq (Nat.mod (2 * g + 1) 2) 0 = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
    change ¬ (2 * g + 1) % 2 = 0
    omega
  have d0 : Nat.div (2 * g) 2 = g := by
    change 2 * g / 2 = g
    omega
  have d1 : Nat.div (2 * g + 1) 2 = g := by
    change (2 * g + 1) / 2 = g
    omega
  rw [h0, h1, cond_true, cond_false, d0, d1]
  exact ⟨rfl, rfl⟩

theorem nl_all {e : Nat} (he : e < 6) : nl e = true := by
  interval_cases e
  exacts [cn16966bnl0, cn16966bnl1, cn16966bnl2, cn16966bnl3, cn16966bnl4, cn16966bnl5]

theorem cv_all {p : Nat} (hp : p < 15) : cv p = true := by
  interval_cases p
  exacts [cn16966bcv0, cn16966bcv1, cn16966bcv2, cn16966bcv3, cn16966bcv4, cn16966bcv5,
    cn16966bcv6, cn16966bcv7, cn16966bcv8, cn16966bcv9, cn16966bcv10, cn16966bcv11,
    cn16966bcv12, cn16966bcv13, cn16966bcv14]

theorem rp_all {e : Nat} (he : e < 6) : rp e = true := by
  interval_cases e
  exacts [cn16966brp0, cn16966brp1, cn16966brp2, cn16966brp3, cn16966brp4, cn16966brp5]

theorem lists_spec : UQ.length = 15 ∧ (∀ m ∈ UQ, m < 32) ∧
    (∀ m < 32, unitP CFSG.KD.GUC1.TH (subQ L m) = true → m = 0 ∨ m ∈ UQ) ∧ lenN RC = 30 ∧
    ∀ c < 30, mulP (nthD 0 RC c) (nthD 0 RCI c) = idP := by
  have h := cn16966b_lists
  unfold lists at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, ltAll_iff, allBelow_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun m hm hu => ?_, by rw [lenN_eq]; exact h4, h5⟩
  have := h3 m hm
  simp only [Bool.or_eq_true, Bool.not_eq_true', hu, Nat.beq_eq, memN_iff] at this
  rcases this with (h | h) | h
  · exact absurd h (by simp)
  · exact Or.inl h
  · exact Or.inr h

theorem d0K_lt : ∀ v ∈ D0K, v < 4096 := by decide

theorem linP_TH1 (v : V12) : linP CFSG.KD.GUC1.TH v = theta0 v := by
  rw [CFSG.KD.GUC1.cg_eq.2]
  exact CFSG.KD.GUTB.linP_TH v

theorem nlk : ∀ U ∈ lGrp NLG 3, NLK L D0K U :=
  nl_of linP_TH1 d0K_lt ct16966b_inv (fun _ hg => letN_spec hg) fun _ he => nl_all he

theorem nl_mem {U : GL} (hU : U ∈ lGrp NLG 3) :
    U ∈ gammaU ∧ U (vecOf a0) = vecOf a0 ∧ (∀ y, U y ∈ spanOf d0 ↔ y ∈ spanOf d0) ∧
      ∀ l, RowsSet (compOf 1) (U * l * U⁻¹) ↔ RowsSet (compOf 1) l := by
  obtain ⟨h1, h2, h3, h4⟩ := nlk U hU
  have hd : D0K = d0 := rfl
  rw [hd] at h3
  have hL : L = five CFSG.KD.GUC0.CG 1 := by
    unfold L
    rw [CFSG.KD.GUC1.cg_eq.1]
  refine ⟨h1, h2, h3, fun l => ?_⟩
  rw [rowsSet_iff (by norm_num) hL, rowsSet_iff (by norm_num) hL]
  exact h4 l

theorem cover {a b : Nat} (ha : a < 32) (hb : b < 32) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b)
    (hua : unitP CFSG.KD.GUC1.TH (subQ L a) = true) (hub : unitP CFSG.KD.GUC1.TH (subQ L b) = true) :
    ∃ k < 2, ∃ U ∈ lGrp NLG 3,
      (∀ v, linP (subQ L a) (U v) = U (linP (subQ L (nthD 0 PM (2 * k))) v)) ∧
        ∀ v, linP (subQ L b) (U v) = U (linP (subQ L (nthD 0 PM (2 * k + 1))) v) := by
  obtain ⟨hlen, -, hcov, -, -⟩ := lists_spec
  have hpos : ∀ m < 32, m ≠ 0 → unitP CFSG.KD.GUC1.TH (subQ L m) = true →
      ∃ p < 15, nthD 0 UQ p = m := by
    intro m hm hm0 hu
    rcases hcov m hm hu with h | h
    · exact absurd h hm0
    · obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem h
      exact ⟨p, by rw [← hlen]; exact hp, by rw [nthD_eq, getD_of_lt _ hp]⟩
  obtain ⟨p, hp, rfl⟩ := hpos a ha ha0 hua
  obtain ⟨q, hq, rfl⟩ := hpos b hb hb0 hub
  have hpq : p ≠ q := fun h => hab (by rw [h])
  have hrow := (allBelow_iff _ _).1 (cv_all hp) q hq
  have hbeq : Nat.beq p q = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
    exact hpq
  rw [hbeq, Bool.false_or] at hrow
  unfold cvOK at hrow
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at hrow
  obtain ⟨⟨hk, hw⟩, hat⟩ := hrow
  obtain ⟨U, hUm, hUP⟩ := CFSG.KD.GUTB.isP_wordP ct16966b_inv _ hw
  exact ⟨_, hk, U, hUm, cvAt_spec hat hUP⟩

theorem res_perm : ∀ U ∈ lGrp NLG 3, ResP (ResPair.n2 1) RC U := by
  obtain ⟨-, -, -, hlen, hRC⟩ := lists_spec
  have hlet : ∀ e < 6, ∀ V, IsP V (letN e) → ResP (ResPair.n2 1) RC V := fun e he V hV =>
    resP_letter (rp_all he) hlen hRC CFSG.KD.GUP1.n2_mem (fun M hM => CFSG.KD.GUP1.n2_le' hM) hV
  refine lGrp_ind _ (resP_one _ _) (fun _ _ => resP_mul hRC) fun g hg U hU => ?_
  have hUi : IsP U⁻¹ (look NLGI g) := hU.inv (invOK_spec _ _ ct16966b_inv g hg)
  obtain ⟨h0, h1⟩ := letN_spec hg
  exact ⟨hlet (2 * g) (by omega) U (by rw [h0]; exact hU),
    hlet (2 * g + 1) (by omega) U⁻¹ (by rw [h1]; exact hUi)⟩

end CFSG.KD.GUN1

end
