module

public import Certificates.Kernel.GammaU.FrameCOK
public import Certificates.Kernel.GammaU.BaseBridge
public import Certificates.Kernel.GammaU.Triple
public import Certificates.Kernel.GammaU.Orb16963OK
public import CFSG.Certificates.Kernel.GammaUFrameCSound
public import CFSG.GF2Type.Smith1979.GammaU.FrameCensusDefs

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUFB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4L CFSG.KD.IF4L CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS
open CFSG.KC.GUF CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem five_comm {c : Nat} (hc : c < 32) :
    ∀ g ∈ five CFSG.KD.GUC0.CG c, ∀ h ∈ five CFSG.KD.GUC0.CG c, ∀ v,
      linP g (linP h v) = linP h (linP g v) := by
  have hex := CFSG.KD.GUCB.exists_isP_cg c hc
  have hF := forall₂_autP hex
  have h := (allBelow_iff _ _).1 CFSG.KD.GUCB.cb16966_cg c hc
  rw [Bool.and_eq_true] at h
  have hci := commInv_of hF h.1
  intro g hg k hk v
  have hgP := isP_autP (hex g hg)
  have hkP := isP_autP (hex k hk)
  have e : autP g (autP k v) = autP k (autP g v) := congrArg (fun U : GL => U v)
    ((hci (autP g) (List.mem_map_of_mem hg)).2 (autP k) (List.mem_map_of_mem hk))
  rw [hkP v, hgP v, hgP (linP k v), hkP (linP g v)] at e
  exact e

theorem frT_TB {c : Nat} (hc : c < 32) :
    FrT (fun m => look CFSG.KD.GUCC.TB (32 * c + m)) (compOf c) := by
  have hex := CFSG.KD.GUCB.exists_isP_cg c hc
  have hF := forall₂_autP hex
  have htb := tbOK_spec CFSG.KD.GUCC.cc16966c_tb c hc
  obtain ⟨h1, h2⟩ := CFSG.KD.GUTB.compOf_iff hc
  refine ⟨fun m hm => ⟨⟨subG ((five CFSG.KD.GUC0.CG c).map autP) m, ?_⟩, ?_⟩,
    fun l => ⟨fun hl => ?_, ?_⟩⟩
  · have := isP_subG hF m
    rw [← htb m hm] at this
    exact this
  · obtain ⟨a, b, hab⟩ : ∃ a b, subP (five CFSG.KD.GUC0.CG c) m = mulP a b := ⟨_, _, rfl⟩
    exact ⟨a, b, (htb m hm).trans hab⟩
  · have hp := CFSG.KD.GUBB.mem_pGrp_of_rows hc hl
    obtain ⟨r, hr, hlr⟩ := hl
    obtain ⟨m, -, hmv⟩ := h2 r hr
    obtain ⟨a, b, hab⟩ : ∃ a b, subQ (five CFSG.KD.GUC0.CG c) m = mulP a b := ⟨_, _, rfl⟩
    have hlP : IsP l (mulP a b) := fun v => by rw [hlr, hmv, hab]
    obtain ⟨m', hm', he⟩ := CFSG.KD.GUCC.mem_TB hc hp hlP
    have hl' : IsP l (look CFSG.KD.GUCC.TB (32 * c + m')) := by
      rw [he]
      exact hlP
    exact ⟨m', hm', hl'⟩
  · rintro ⟨m, hm, hlm⟩
    have hlm' : IsP l (subP (five CFSG.KD.GUC0.CG c) m) := by
      rw [← htb m hm]
      exact hlm
    obtain ⟨x, hx, hxv⟩ := h1 m
    exact ⟨x, hx, fun v => by rw [hlm' v, linP_subP_subQ (five_comm hc) m v, hxv]⟩

theorem frT_LT {i LT : Nat} (hi : i < 32) (h : ltOK CFSG.KD.GUCC.TB i LT = true) :
    FrT (look LT) (compOf i) :=
  frT_congr (frT_TB hi) fun m hm => (ltOK_spec h m hm).1

theorem cg_rows {c l : Nat} (hc : c < 32) (hl : l < 5) :
    ∃ V : GL, IsP V (look CFSG.KD.GUC0.CG (5 * c + l)) ∧ RowsSet (compOf c) V := by
  obtain ⟨V, hV⟩ := CFSG.KD.GUCB.exists_isP_cg c hc _ (mem_five.2 ⟨l, hl, rfl⟩)
  have hmem : (ResPair.compGens c).getD l #[] ∈ ResPair.compGens c := by
    rw [List.getD_eq_getElem _ _ (by rw [CFSG.KD.GUCB.length_compGens]; exact hl)]
    exact List.getElem_mem _
  exact ⟨V, hV, CFSG.KD.GUBB.rowsSet_gen hmem fun x => (hV x).trans (CFSG.KD.GUCB.linP_cg hc hl x)⟩

theorem n2_letters {i : Nat} {N2 : List Nat} {NA NN : Nat}
    (hN2 : N2 = (ResPair.n2Gens i).map packR)
    (hrows : ((ResPair.n2Gens i).all fun r => rowsOK r.toList) = true)
    (h : n2OK CFSG.KD.GUC0.TH N2 NA NN = true) :
    ∀ e < NN + NN, ∃ U ∈ ResPair.n2 i, IsP U (look NA e) := by
  obtain ⟨hlen, hq⟩ := n2OK_spec h
  have hlen' : (ResPair.n2Gens i).length = NN := by rw [← hlen, hN2, List.length_map]
  have hmem : ∀ q < NN, ∃ U ∈ ResPair.n2 i, IsP U (look NA q) := by
    intro q hq'
    obtain ⟨he, -, hinv⟩ := hq q hq'
    obtain ⟨U, hU⟩ := IsP.exists_of_mul hinv
    have hql : q < (ResPair.n2Gens i).length := by rw [hlen']; exact hq'
    have hU' := hU
    rw [he, hN2, nthD_map _ _ _ #[] hql] at hU'
    have hm : (ResPair.n2Gens i).getD q #[] ∈ ResPair.n2Gens i := by
      rw [getD_of_lt _ hql]
      exact List.getElem_mem hql
    refine ⟨U, ?_, hU⟩
    rw [ResPair.n2, Viol.genGrp]
    exact Subgroup.subset_closure ⟨_, hm, (isP_packR (List.all_eq_true.1 hrows _ hm) U).1 hU'⟩
  intro e he
  by_cases hlt : e < NN
  · exact hmem e hlt
  · obtain ⟨q, rfl⟩ : ∃ q, e = NN + q := ⟨e - NN, by omega⟩
    obtain ⟨U, hU, hUP⟩ := hmem q (by omega)
    exact ⟨U⁻¹, inv_mem hU, hUP.inv (hq q (by omega)).2.2⟩

theorem n2_le_gammaU {i : Nat} {N2 : List Nat} {NA NN : Nat}
    (hN2 : N2 = (ResPair.n2Gens i).map packR)
    (hrows : ((ResPair.n2Gens i).all fun r => rowsOK r.toList) = true)
    (h : n2OK CFSG.KD.GUC0.TH N2 NA NN = true) : ResPair.n2 i ≤ gammaU := by
  obtain ⟨hlen, hq⟩ := n2OK_spec h
  rw [ResPair.n2, Viol.genGrp, Subgroup.closure_le]
  rintro V ⟨r, hr, hVr⟩
  obtain ⟨q, hql, rfl⟩ := List.getElem_of_mem hr
  have hq' : q < NN := by rw [← hlen, hN2, List.length_map]; exact hql
  obtain ⟨he, hgu, -⟩ := hq q hq'
  have hP : IsP V (look NA q) := by
    rw [he, hN2, nthD_map _ _ _ #[] hql, getD_of_lt _ hql]
    exact (isP_packR (List.all_eq_true.1 hrows _ hr) V).2 hVr
  exact guOK_spec CFSG.KD.GUTB.linP_TH hgu hP

theorem hyp_rows {i LT : Nat} {HM : List Nat} (hi : i < 32)
    (hlt : ltOK CFSG.KD.GUCC.TB i LT = true) (hHM : ∀ q ∈ HM, q < 32)
    (heq : HM.map (subQ (five CFSG.KD.GUC0.CG i)) = (ResPair.hyp10 i).map packR)
    (hrows : ((ResPair.hyp10 i).all fun r => rowsOK r.toList) = true) :
    ∀ r ∈ idR :: ResPair.hyp10 i,
      (∀ v, linOfRows r v = v) ∨ ∃ q ∈ HM, ∀ v, linOfRows r v = linP (look LT q) v := by
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr
  · exact Or.inl fun v => linOfRows_idR v
  · right
    have hm : packR r ∈ HM.map (subQ (five CFSG.KD.GUC0.CG i)) := by
      rw [heq]
      exact List.mem_map_of_mem hr
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hm
    refine ⟨q, hq, fun v => ?_⟩
    rw [← linP_eq_of_rowsP (rowsP_packR (List.all_eq_true.1 hrows _ hr)) v, ← hqe,
      (ltOK_spec hlt q (hHM q hq)).1, tbOK_spec CFSG.KD.GUCC.cc16966c_tb i hi q (hHM q hq),
      linP_subP_subQ (five_comm hi)]

theorem d0_facts : (∀ y ∈ spanOf d0, q0 y = 0) ∧ Module.finrank (ZMod 2) (spanOf d0) = 6 := by
  obtain ⟨-, -, -, hR, -⟩ := CFSG.KD.GUO.co16963_pin
  have hB := CFSG.KC.GUO.repF_spec CFSG.KD.GUO.co16963_r1
  rw [hR] at hB
  have e : nthD [] dReps 1 = d0 := by decide
  rw [e] at hB
  exact ⟨hB.ts, hB.finrank⟩

theorem facts_of {i : Nat} (hi : i < 32) {PG : List Nat} {NA NN NN2 LT RW RWi : Nat}
    {RP RJ HM : List Nat} {SR : List (List (List (List Nat)))} {CV : List (List (List Nat))}
    {TR : List (List Nat)} {N2 : List Nat} (hNN2 : NN2 = NN + NN)
    (hN2 : N2 = (ResPair.n2Gens i).map packR)
    (hrows : ((ResPair.n2Gens i).all fun r => rowsOK r.toList) = true)
    (hHMeq : HM.map (subQ (five CFSG.KD.GUC0.CG i)) = (ResPair.hyp10 i).map packR)
    (hHrows : ((ResPair.hyp10 i).all fun r => rowsOK r.toList) = true)
    (hn2 : n2OK CFSG.KD.GUC0.TH N2 NA NN = true) (hpg : pgOK CFSG.KD.GUC0.TH PG = true)
    (hlt : ltOK CFSG.KD.GUCC.TB i LT = true) (htree : treeOK NA NN CFSG.KD.GUO.SM PG TR = true)
    (hHM : ∀ q ∈ HM, q < 32)
    (hcv : ∀ p < PG.length, cvOK NA NN2 CFSG.KD.GUCC.DT RP RW PG CV p = true)
    (hfr : ∀ r < RP.length, nthD 0 RP r < PG.length →
      repOK CFSG.KD.GUC0.TH NA NN2 HM CFSG.KD.GUCC.TB CFSG.KD.GUC0.CG LT CFSG.KD.GUFC0.PT
        CFSG.KD.GUFC0.CM PG CFSG.KD.GUCC.DT RP RJ RW RWi SR r = true) :
    FrameCensusFacts i := by
  have hTH := CFSG.KD.GUTB.linP_TH
  have hN := n2_letters hN2 hrows hn2
  have hN' : ∀ e < NN2, ∃ U ∈ ResPair.n2 i, IsP U (look NA e) := by
    rw [hNN2]
    exact hN
  have hNg := n2_le_gammaU hN2 hrows hn2
  have hpgs := pgOK_spec hpg
  have hPG : ∀ g ∈ PG, IsP (autP g) g ∧ autP g ∈ gammaU := fun g hg => by
    obtain ⟨U, hU, hUg⟩ := CFSG.KC.GUO.exists_of_guOK hTH (hpgs g hg)
    rw [IsP.inj (isP_autP ⟨U, hU⟩) hU]
    exact ⟨hU, hUg⟩
  have hLi := frT_LT hi hlt
  have hLT : ∀ m < 32, rd (look LT m) = m := fun m hm => (ltOK_spec hlt m hm).2
  have hH := hyp_rows hi hlt hHM hHMeq hHrows
  refine ⟨CFSG.KD.GUBB.TD, 108, CFSG.KD.GUBB.frameTr, PG.map autP, fun g hg => ?_, hNg,
    fun x hx0 hxq => ?_, fun g hg j hj => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
    exact (hPG y hy).2
  ·
    have hNN : ∀ l < NN, ∃ U ∈ ResPair.n2 i, IsP U (look NA l) := fun l hl => hN l (by omega)
    have hS : ∀ U ∈ ResPair.n2 i, ∀ y : V12,
        (∃ g ∈ PG.map autP, ∃ V ∈ ResPair.n2 i, y = V (g (vecOf a0))) →
          ∃ g ∈ PG.map autP, ∃ V ∈ ResPair.n2 i, U y = V (g (vecOf a0)) := by
      rintro U hU y ⟨g, hg, V, hV, rfl⟩
      exact ⟨g, hg, U * V, mul_mem hU hV, rfl⟩
    have hinit : ∀ n, (ptMask PG).testBit n = true →
        ∃ g ∈ PG.map autP, ∃ V ∈ ResPair.n2 i, vecOf n = V (g (vecOf a0)) := by
      intro n hn
      obtain ⟨g, hg, e⟩ := ptMask_spec hn
      refine ⟨autP g, List.mem_map_of_mem hg, 1, one_mem _, ?_⟩
      change vecOf n = autP g (vecOf a0)
      rw [ha0, (hPG g hg).1.apply_code, e]
    have hn := codeOf_lt x
    have hvn := vecOf_codeOf x
    have hn0 : codeOf x ≠ 0 := fun h => hx0 (by rw [← hvn, h, vecOf_zero])
    have hqk : CFSG.KC.GUO.q0k (codeOf x) = 0 :=
      (CFSG.KC.GUO.q0k_zero_iff _).2 (by rw [hvn]; exact hxq)
    have hbit : CFSG.KD.GUO.SM.testBit (codeOf x) = true := by
      have h := (allBelow_iff _ _).1 CFSG.KD.GUO.co16963_sm _ hn
      have e := Nat.eq_of_beq_eq_true h
      cases hb : Nat.beq (codeOf x) 0
      · rw [hb, hqk] at e
        exact CFSG.KC.GUO.testBit_of_land e
      · exact absurd (Nat.eq_of_beq_eq_true hb) hn0
    obtain ⟨g, hg, V, hV, e⟩ := treeN_spec hNN
      (S := fun y => ∃ g ∈ PG.map autP, ∃ V ∈ ResPair.n2 i, y = V (g (vecOf a0))) hS TR
      (ptMask PG) htree hinit _ hbit
    refine ⟨g, hg, V, hV, ?_⟩
    rw [← e, hvn]
  ·
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    obtain ⟨p, hp, hpx⟩ := List.getElem_of_mem hx
    have hxp : nthD 0 PG p = x := by rw [nthD_eq, getD_of_lt _ hp, hpx]
    obtain ⟨rec, hr, hrp, hw, hcvAt⟩ := cvOK_spec (hcv p hp) j hj
    obtain ⟨hj', -, hRW, hrep⟩ := repOK_spec (hfr _ hr (by rw [hrp]; exact hp))
    rw [hrp, hxp] at hRW
    rw [hxp] at hcvAt
    have hTj' := CFSG.KD.GUBB.isP_TD hj'
    have hTj := CFSG.KD.GUBB.isP_TD hj
    have hW : IsP (autP x * CFSG.KD.GUBB.TD (nthD 0 RJ (nthD 0 rec 0))) (look RW (nthD 0 rec 0)) := by
      rw [hRW]
      exact (hPG x hx).1.mul hTj'
    have hWg : autP x * CFSG.KD.GUBB.TD (nthD 0 RJ (nthD 0 rec 0)) ∈ gammaU :=
      mul_mem (hPG x hx).2 (CFSG.KD.GUF.dt_mem hj' hTj').1
    have hAg : autP x * CFSG.KD.GUBB.TD j ∈ gammaU :=
      mul_mem (hPG x hx).2 (CFSG.KD.GUF.dt_mem hj hTj).1
    obtain ⟨M, hM, hMx, hE⟩ := cvAt_spec hcvAt hN' hw hNg hW
      (A := autP x * CFSG.KD.GUBB.TD j)
      (fun v => by rw [LinearEquiv.mul_apply, hTj v, (hPG x hx).1]) hWg hAg d0_facts
    refine ⟨M, hM, ?_, _, hj', hE, fun c hc => ?_⟩
    · rw [ha0, (hPG x hx).1.apply_code]
      exact hMx
    · unfold FrameGood
      exact repAt_spec hrep hTH CFSG.KD.GUFC0.cf16982_pc hN' hW hLi hLT (Lc := compOf)
        (fun c hc => frT_TB hc) (fun c hc l hl => cg_rows hc hl) hHM hH c hc

end CFSG.KD.GUFB

namespace CFSG.KD.GUFC0

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.KC.GUF CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.GammaU.StepA

theorem cf16982a_h10r :
    ((ResPair.hyp10 0).all fun r => CFSG.KC.GUS.rowsOK r.toList) = true := by decide +kernel

theorem frameCensusFacts0 : FrameCensusFacts 0 := by
  have hl := cf16982a_lists
  unfold lists at hl
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, ltAll_iff] at hl
  obtain ⟨⟨⟨⟨hPG, -⟩, -⟩, -⟩, hHM⟩ := hl
  refine CFSG.KD.GUFB.facts_of (RJ := RJ) (RWi := RWi) (SR := SR) (by norm_num) rfl
    CFSG.KD.GUT0.ct16966a_n2
    CFSG.KD.GUS0.cs16981a_rows CFSG.KD.GUT0.hm_eq cf16982a_h10r cf16982a_n2 cf16982a_pg cf16982a_lt
    cf16982a_tree hHM (fun p hp => cf16982a_cvall p (by rw [hPG] at hp; exact hp))
    (fun r hr hp => ?_)
  have h := (allBelow_iff _ _).1 (cf16982a_frall (nthD 0 RP r) (by rw [hPG] at hp; exact hp)) r
    (by rw [lenN_eq]; exact hr)
  simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at h
  exact h

end CFSG.KD.GUFC0

namespace CFSG.KD.GUFC1

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.KC.GUF CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.GammaU.StepA

theorem cf16982b_h10r :
    ((ResPair.hyp10 1).all fun r => CFSG.KC.GUS.rowsOK r.toList) = true := by decide +kernel

theorem frameCensusFacts1 : FrameCensusFacts 1 := by
  have hl := cf16982b_lists
  unfold lists at hl
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, ltAll_iff] at hl
  obtain ⟨⟨⟨⟨hPG, -⟩, -⟩, -⟩, hHM⟩ := hl
  have hm : CFSG.KD.GUT1.HM.map (subQ (CFSG.KC.GUC.five CFSG.KD.GUC0.CG 1)) =
      (ResPair.hyp10 1).map CFSG.KC.IF4R.packR := by
    have := CFSG.KD.GUT1.hm_eq
    unfold CFSG.KD.GUT1.L at this
    rw [CFSG.KD.GUC1.cg_eq.1] at this
    exact this
  refine CFSG.KD.GUFB.facts_of (RJ := RJ) (RWi := RWi) (SR := SR) (by norm_num) rfl
    CFSG.KD.GUT1.ct16966b_n2
    CFSG.KD.GUS1.cs16981b_rows hm cf16982b_h10r cf16982b_n2 cf16982b_pg cf16982b_lt
    cf16982b_tree hHM (fun p hp => cf16982b_cvall p (by rw [hPG] at hp; exact hp))
    (fun r hr hp => ?_)
  have h := (allBelow_iff _ _).1 (cf16982b_frall (nthD 0 RP r) (by rw [hPG] at hp; exact hp)) r
    (by rw [lenN_eq]; exact hr)
  simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at h
  exact h

end CFSG.KD.GUFC1

namespace CFSG.KD.GUFC

theorem frameCensusFacts : ∀ i, i = 0 ∨ i = 1 → CFSG.GF2Type.Smith1979.GammaU.StepA.FrameCensusFacts i
  | _, Or.inl rfl => CFSG.KD.GUFC0.frameCensusFacts0
  | _, Or.inr rfl => CFSG.KD.GUFC1.frameCensusFacts1

end CFSG.KD.GUFC

end
