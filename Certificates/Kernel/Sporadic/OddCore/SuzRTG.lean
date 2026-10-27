module

public import Certificates.Kernel.Sporadic.OddCore.SuzRTF
public import CFSG.Certificates.Kernel.Spor.OrbElems

public section

namespace CertificateChecks.KernelSpor.SuzRTG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs CFSG.KS.KeyBfsG CFSG.KS.OrbElems
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.RootTwistCheck
open CFSG.Sporadic.SuzRecog.RootTwistData CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck (conjA t1A commA)
open CFSG.Sporadic.SuzRecog.LevelTwo (actV Elt eltOne genP genQ elPq elQp eltPin orbitElems)
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzRTK
open CertificateChecks.KernelSpor.L2K
open CertificateChecks.KernelSpor.SuzRTF
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P commA_P)
open CertificateChecks.KernelSpor.L2G (sB band bif_true nbeq nblt nble nblt_f allN_get)

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Idn" => pidn 1782 11

theorem actK_sound {g gi : Array Nat} {G GI v y : Nat} (hg : P g G) (hgi : P gi GI)
    (h : actK G GI v y = true) : actV g gi v = y := by
  unfold actK at h
  rw [bif_true] at h
  by_cases hvl : v < 2835
  · have h1 := h.1 (nblt.2 hvl)
    rw [band, nblt, nbeq] at h1
    unfold actV
    simp only [hvl, ↓reduceIte]
    rw [(L2G.pA hvA hvl).1, hg.1, hgi.1,
      L2G.fpConj_unpack hg.2 hgi.2 (L2G.pA hvA hvl).2, ← h1.2]
    exact L2G.aIdx_get hvA L2G.vtxOK.sA h1.1
  · have h1 := h.2 (nblt_f hvl)
    rw [band, band, band, band, nble, nblt, nble, nblt, sB, sB] at h1
    obtain ⟨-, hv2, hy1, hy2, h3⟩ := h1
    generalize hf : fpCK 11 (mask 11) G GI (TK (Nat.sub v 2835) 0) = f at h3
    generalize hb : Nat.mul 3 (Nat.sub y 2835) = b at h3
    clear h
    have hj : v - 2835 < 162 := Nat.sub_lt_left_of_lt_add (by omega) (by omega)
    have hj' : y - 2835 < 162 := Nat.sub_lt_left_of_lt_add hy1 (by omega)
    have hb' : 3 * (y - 2835) = b := hb
    have hf' : fpCK 11 (mask 11) G GI (TK (v - 2835) 0) = f := hf
    have key : ∃ k < 3, fT (b + k) = f := by
      simp only [bif_true, nbeq] at h3
      by_cases e0 : fT b = f
      · exact ⟨0, by norm_num, by rw [Nat.add_zero]; exact e0⟩
      · have h3' := h3.2 (Q3AG.nbeq_false e0)
        by_cases e1 : fT (Nat.add b 1) = f
        · exact ⟨1, by norm_num, e1⟩
        · exact ⟨2, by norm_num, h3'.2 (Q3AG.nbeq_false e1)⟩
    obtain ⟨k, hk, hfk⟩ := key
    unfold actV
    simp only [hvl, ↓reduceIte]
    rw [(L2G.pW hvW hj).1, hg.1, hgi.1, L2G.fpConj_unpack hg.2 hgi.2 (L2G.pW hvW hj).2, hf',
      ← hfk, ← hb', L2G.vIdx_get hvW L2G.vtxOK.sT hj' hk]
    omega

theorem orb_rec {o off cnt b : Nat} {gs : Array Elt} (hgs : gs.size = 6)
    (hg : ∀ s < 6, P gs[s]!.1 (L2EL.F (off + s)) ∧ P gs[s]!.2 (L2EI (off + s)))
    (hh : oHd o b cnt = true) (hp : ∀ i < cnt, oPt o off cnt i = true) (hcnt : cnt ≤ 2997) :
    (orbKey gs b).1.size = cnt ∧ ∀ i < cnt, (orbKey gs b).1[i]! = oT o i ∧
      (orbKey gs b).2.1[i]! = (if i = 0 then 0 else oPL o i / 6) ∧
      (orbKey gs b).2.2[i]! = (if i = 0 then 0 else oPL o i % 6) := by
  unfold oHd at hh
  rw [band, nbeq, nblt] at hh
  obtain ⟨hT0, hc0⟩ := hh
  have sp : ∀ i < cnt, oT o i < 2997 ∧ oVP o (oT o i) = i ∧
      (i ≠ 0 → oPL o i / 6 < i ∧ oPOS o (oPL o i) = i ∧
        (i + 1 < cnt → oPL o i < oPL o (i + 1))) ∧
      (∀ s < 6, oPOS o (6 * i + s) < cnt ∧
        actV gs[s]!.1 gs[s]!.2 (oT o i) = oT o (oPOS o (6 * i + s)) ∧
        (oPOS o (6 * i + s) = 0 ∨ oPL o (oPOS o (6 * i + s)) ≤ 6 * i + s)) := by
    intro i hi
    have h := hp i hi
    unfold oPt at h
    simp only [strictB_eq, bAnd_iff] at h
    obtain ⟨a1, a2, a3, a4⟩ := h
    refine ⟨blt_true a1, Nat.eq_of_beq_eq_true a2, fun h0 => ?_, fun s hs => ?_⟩
    · have hz : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
      rw [hz] at a3
      simp only [bAnd_iff] at a3
      obtain ⟨b1, b2, b3⟩ := a3
      refine ⟨blt_true b1, Nat.eq_of_beq_eq_true b2, fun h1 => ?_⟩
      have hb : Nat.blt (Nat.succ i) cnt = true := by simpa [Nat.blt_eq] using h1
      rw [hb] at b3
      exact blt_true b3
    · have h := allN_spec a4 s hs
      simp only [bAnd_iff] at h
      obtain ⟨b1, b2, b3⟩ := h
      refine ⟨blt_true b1, actK_sound (hg s hs).1 (hg s hs).2 b2, ?_⟩
      by_cases hz : oPOS o (6 * i + s) = 0
      · exact Or.inl hz
      · have hz' : Nat.beq (oPOS o (Nat.add (Nat.mul 6 i) s)) 0 = false :=
          Bool.eq_false_iff.2 fun e => hz (Nat.eq_of_beq_eq_true e)
        rw [hz'] at b3
        exact Or.inr (by simpa [Nat.ble_eq] using b3)
  have hdm : ∀ c, 6 * (c / 6) + c % 6 = c := fun c => Nat.div_add_mod c 6
  have Rec : GRec (fun x => x) (orbSt gs) 6 b b cnt (6 * cnt) (oT o)
      (fun i => if i = 0 then 0 else oPL o i / 6) (fun i => if i = 0 then 0 else oPL o i % 6)
      (oPOS o) := by
    refine ⟨by norm_num, hc0, hT0, rfl, by simp, by simp, fun a ha c hc e => ?_,
      fun i h0 hi => ?_, fun i h0 hi => ?_, ?_, fun e he => ?_⟩
    · rw [← (sp a ha).2.1, ← (sp c hc).2.1]
      exact congrArg (oVP o) e
    · obtain ⟨b1, b2, -⟩ := (sp i hi).2.2.1 (by omega)
      simp only [Nat.pos_iff_ne_zero.1 h0, ↓reduceIte]
      refine ⟨b1, Nat.mod_lt _ (by norm_num), ?_⟩
      have := ((sp (oPL o i / 6) (by omega)).2.2.2 (oPL o i % 6) (Nat.mod_lt _ (by norm_num))).2.1
      rw [hdm, b2] at this
      exact this.symm
    · have h1 : i + 1 ≠ 0 := by omega
      simp only [Nat.pos_iff_ne_zero.1 h0, h1, ↓reduceIte, hdm]
      exact ((sp i (by omega)).2.2.1 (by omega)).2.2 hi
    · by_cases h1 : cnt - 1 = 0
      · simp only [h1, ↓reduceIte]
        omega
      · simp only [h1, ↓reduceIte]
        have := ((sp (cnt - 1) (by omega)).2.2.1 h1).1
        omega
    · have hed : e / 6 < cnt := by omega
      have hek : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
      obtain ⟨c1, c2, c3⟩ := (sp (e / 6) hed).2.2.2 (e % 6) hek
      rw [hdm e] at c1 c2 c3
      refine ⟨c1, c2, ?_⟩
      rcases c3 with z | z
      · exact Or.inl z
      · by_cases hz : oPOS o e = 0
        · exact Or.inl hz
        · right
          simp only [hz, ↓reduceIte, hdm]
          exact z
  have hcap : (if cnt - 1 = 0 then 0 else oPL o (cnt - 1) / 6) < 2997 := by
    by_cases h1 : cnt - 1 = 0
    · simp only [h1, ↓reduceIte]
      omega
    · simp only [h1, ↓reduceIte]
      have := ((sp (cnt - 1) (by omega)).2.2.1 h1).1
      omega
  have R := keyBfsG_rec Rec hcap
  unfold orbKey
  rw [hgs]
  exact ⟨R.2.2.1 (le_refl _), fun i hi => R.2.1 i hi⟩

theorem stE_P {gs : Array Elt} {k off : Nat} {u : Elt} {U UI : Nat}
    (hg : P gs[k]!.1 (L2EL.F (off + k)) ∧ P gs[k]!.2 (L2EI (off + k))) (hu : P u.1 U ∧ P u.2 UI) :
    P (stE gs k u).1 (pc (L2EL.F (off + k)) U) ∧ P (stE gs k u).2 (pc UI (L2EI (off + k))) := by
  unfold stE
  dsimp only
  exact ⟨p_comp hg.1 hu.1, p_comp hu.2 hg.2⟩

theorem one_P : P eltOne.1 Idn ∧ P eltOne.2 Idn := by
  unfold eltOne
  dsimp only
  exact ⟨pidn_P, pidn_P⟩

theorem hgP : ∀ s < 6, P genP[s]!.1 (L2EL.F (0 + s)) ∧ P genP[s]!.2 (L2EI (0 + s)) := by
  intro s hs
  rw [L2G.genP_get hs, Nat.zero_add]
  exact ⟨(L2G.eltP (by omega)).1, (L2G.eltP (by omega)).2.1⟩

theorem hgQ : ∀ s < 6, P genQ[s]!.1 (L2EL.F (6 + s)) ∧ P genQ[s]!.2 (L2EI (6 + s)) := by
  intro s hs
  rw [L2G.genQ_get hs]
  exact ⟨(L2G.eltP (by omega)).1, (L2G.eltP (by omega)).2.1⟩

theorem orb_get {o off cnt b : Nat} {gs : Array Elt} (hgs : gs.size = 6)
    (hg : ∀ s < 6, P gs[s]!.1 (L2EL.F (off + s)) ∧ P gs[s]!.2 (L2EI (off + s)))
    (hh : oHd o b cnt = true) (hp : ∀ i < cnt, oPt o off cnt i = true) (hcnt : cnt ≤ 2997) :
    (orbitElems gs b).getD (oT o 0) eltOne = eltOne ∧
      ∀ i < cnt, 0 < i → (orbitElems gs b).getD (oT o i) eltOne =
        stE gs (oPL o i % 6) ((orbitElems gs b).getD (oT o (oPL o i / 6)) eltOne) := by
  obtain ⟨hs, hr⟩ := orb_rec hgs hg hh hp hcnt
  obtain ⟨t0, t1⟩ := orbitElems_tree gs b
  have hc0 : 0 < cnt := by
    unfold oHd at hh
    rw [band, nblt] at hh
    exact hh.2
  refine ⟨by rw [← (hr 0 hc0).1]; exact t0, fun i hi h0 => ?_⟩
  obtain ⟨a1, a2, a3⟩ := t1 i (by omega) h0
  obtain ⟨e1, e2, e3⟩ := hr i hi
  have hz : i ≠ 0 := by omega
  rw [e2] at a1 a3
  rw [e3] at a3
  simp only [hz, ↓reduceIte] at a1 a3
  rw [e1, (hr _ (by omega)).1] at a3
  exact a3

theorem genP_size : genP.size = 6 := by simp [CFSG.Sporadic.SuzRecog.LevelTwo.genP]

theorem genQ_size : genQ.size = 6 := by simp [CFSG.Sporadic.SuzRecog.LevelTwo.genQ]

theorem getP : elPq.getD (oT 0 0) eltOne = eltOne ∧
    ∀ i < 18, 0 < i → elPq.getD (oT 0 i) eltOne =
      stE genP (oPL 0 i % 6) (elPq.getD (oT 0 (oPL 0 i / 6)) eltOne) :=
  orb_get (o := 0) (off := 0) (cnt := 18) (b := 2835) genP_size hgP
    ((band (oHd 0 2835 18) (allN 18 (oPt 0 0 18))).1 kOrbP).1
    (fun _ hi => allN_get ((band (oHd 0 2835 18) (allN 18 (oPt 0 0 18))).1 kOrbP).2 hi)
    (by norm_num)

theorem getQ : elQp.getD (oT 1 0) eltOne = eltOne ∧
    ∀ i < 315, 0 < i → elQp.getD (oT 1 i) eltOne =
      stE genQ (oPL 1 i % 6) (elQp.getD (oT 1 (oPL 1 i / 6)) eltOne) :=
  orb_get (o := 1) (off := 6) (cnt := 315) (b := 0) genQ_size hgQ
    ((band (oHd 1 0 315) (allN 315 (oPt 1 6 315))).1 kOrbQ).1
    (fun _ hi => allN_get ((band (oHd 1 0 315) (allN 315 (oPt 1 6 315))).1 kOrbQ).2 hi)
    (by norm_num)

theorem paths : oT 0 11 = 2970 ∧ oPL 0 11 = 6 * 3 + 4 ∧ oPL 0 3 = 6 * 0 + 3 ∧ oT 0 2 = 2890 ∧
    oPL 0 2 = 6 * 0 + 2 ∧ oT 1 61 = 1436 ∧ oPL 1 61 = 6 * 10 + 2 ∧ oPL 1 10 = 6 * 1 + 3 ∧
    oPL 1 1 = 6 * 0 + 0 ∧ oT 1 53 = 1660 ∧ oPL 1 53 = 6 * 8 + 5 ∧ oPL 1 8 = 6 * 1 + 1 := by
  have h := kPath
  unfold pathK at h
  simp only [Bool.and_eq_true, nbeq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem step_of {gs : Array Elt} {m : Std.HashMap Nat Elt} {o i : Nat} {c : Nat}
    (hs : m.getD (oT o i) eltOne = stE gs (oPL o i % 6) (m.getD (oT o (oPL o i / 6)) eltOne))
    (hc : oPL o i = c) :
    m.getD (oT o i) eltOne = stE gs (c % 6) (m.getD (oT o (c / 6)) eltOne) := by
  rw [hs, hc]

theorem hEl_V : P (hEl 2970).1 (eltK [4, 3]) ∧ P (hEl 2970).2 (eltIK [4, 3]) := by
  have e : hEl 2970 = stE genP 4 (stE genP 3 eltOne) := by
    unfold hEl
    rw [← paths.1, step_of (getP.2 11 (by norm_num) (by norm_num)) paths.2.1,
      step_of (getP.2 3 (by norm_num) (by norm_num)) paths.2.2.1, getP.1]
  rw [e]
  exact stE_P (hgP 4 (by norm_num)) (stE_P (hgP 3 (by norm_num)) one_P)

theorem hEl_V' : P (hEl 2890).1 (eltK [2]) ∧ P (hEl 2890).2 (eltIK [2]) := by
  have e : hEl 2890 = stE genP 2 eltOne := by
    unfold hEl
    rw [← paths.2.2.2.1, step_of (getP.2 2 (by norm_num) (by norm_num)) paths.2.2.2.2.1, getP.1]
  rw [e]
  exact stE_P (hgP 2 (by norm_num)) one_P

theorem kEl_V : P (elQp.getD 1436 eltOne).1 (eltK [8, 9, 6]) ∧
    P (elQp.getD 1436 eltOne).2 (eltIK [8, 9, 6]) := by
  have e : elQp.getD 1436 eltOne = stE genQ 2 (stE genQ 3 (stE genQ 0 eltOne)) := by
    rw [← paths.2.2.2.2.2.1, step_of (getQ.2 61 (by norm_num) (by norm_num)) paths.2.2.2.2.2.2.1,
      step_of (getQ.2 10 (by norm_num) (by norm_num)) paths.2.2.2.2.2.2.2.1,
      step_of (getQ.2 1 (by norm_num) (by norm_num)) paths.2.2.2.2.2.2.2.2.1, getQ.1]
  rw [e]
  exact stE_P (hgQ 2 (by norm_num)) (stE_P (hgQ 3 (by norm_num)) (stE_P (hgQ 0 (by norm_num))
    one_P))

theorem kEl_V' : P (elQp.getD 1660 eltOne).1 (eltK [11, 7, 6]) ∧
    P (elQp.getD 1660 eltOne).2 (eltIK [11, 7, 6]) := by
  have e : elQp.getD 1660 eltOne = stE genQ 5 (stE genQ 1 (stE genQ 0 eltOne)) := by
    rw [← paths.2.2.2.2.2.2.2.2.2.1,
      step_of (getQ.2 53 (by norm_num) (by norm_num)) paths.2.2.2.2.2.2.2.2.2.2.1,
      step_of (getQ.2 8 (by norm_num) (by norm_num)) paths.2.2.2.2.2.2.2.2.2.2.2,
      step_of (getQ.2 1 (by norm_num) (by norm_num)) paths.2.2.2.2.2.2.2.2.1, getQ.1]
  rw [e]
  exact stE_P (hgQ 5 (by norm_num)) (stE_P (hgQ 1 (by norm_num)) (stE_P (hgQ 0 (by norm_num))
    one_P))

theorem elemOK_P {g gi : Array Nat} {G GI : Nat} (hg : P g G) (hgi : P gi GI) (hi : ie G GI = true)
    (hm : memXK G = true) : CFSG.Sporadic.SuzRecog.LevelTwo.elemOK g gi = true := by
  unfold CFSG.Sporadic.SuzRecog.LevelTwo.elemOK
  rw [hg.1, hgi.1, (invEqK_sound hi).2, L2XCG.memX_of rfl hg.2 hm]
  rfl

theorem pW0R : P w0RArr W0R := conj_P pRho pRhoI pW0

theorem plusB_P {m : Array Nat} {M MI : Nat} (hm : P m M) (hcMI : cn MI = true)
    (h : plusBK M MI = true) : plusB m = true := by
  unfold plusBK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hie, hc⟩, hn⟩, he⟩ := h
  have hmi := SuzMGF.p_invR hm hie hcMI
  unfold plusB evenAt
  rw [commA_P hm pT1, normV_P pW0 pW0R hm hmi.1,
    commA_P (p_comp hm (powA_P pRhoI 0)) pW0, commA_P (p_comp hm (powA_P pRhoI 0)) pW0R,
    commA_P (p_comp hm (powA_P pRhoI 1)) pW0, commA_P (p_comp hm (powA_P pRhoI 1)) pW0R,
    commA_P (p_comp hm (powA_P pRhoI 2)) pW0, commA_P (p_comp hm (powA_P pRhoI 2)) pW0R]
  simp only [Bool.and_eq_true]
  exact ⟨⟨hc, hn⟩, he⟩

theorem squareOK_of {v : Nat} {m xi : Array Nat} {X XI y : Nat} {ph pk : List Nat}
    (hm : P m X) (hxi : P xi XI)
    (hH : P (hEl v).1 (eltK ph) ∧ P (hEl v).2 (eltIK ph))
    (hK : P (elQp.getD y eltOne).1 (eltK pk) ∧ P (elQp.getD y eltOne).2 (eltIK pk))
    (h : squareK v X XI ph pk y = true) : squareOK v m = true := by
  unfold squareK at h
  simp only [strictB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have hact : actV (hEl v).2 (hEl v).1 CFSG.Sporadic.SuzRecog.LevelTwo.p1 = y := by
    rw [L2G.p1_eq]
    exact actK_sound hH.2 hH.1 h5
  have hu : uEl v = (compA 1782 (hEl v).1 (elQp.getD y eltOne).1,
      compA 1782 (elQp.getD y eltOne).2 (hEl v).2) := by
    unfold uEl
    simp only [hact]
  have hU : P (uEl v).1 (pc (eltK ph) (eltK pk)) ∧ P (uEl v).2 (pc (eltIK pk) (eltIK ph)) := by
    rw [hu]
    dsimp only
    exact ⟨p_comp hH.1 hK.1, p_comp hK.2 hH.2⟩
  have hp1 : CFSG.Sporadic.SuzRecog.LevelTwo.p1 = 342 := L2G.p1_eq
  unfold squareOK CFSG.Sporadic.SuzRecog.LevelTwo.pElemOK conjInvA
  rw [hp1, L2G.sendsB_eq hvA hvW hH.1 hH.2 (by norm_num : 0 < 2997),
    L2G.sendsB_eq hvA hvW hH.1 hH.2 (by norm_num : 2835 < 2997),
    L2G.sendsB_eq hvA hvW hU.1 hU.2 (by norm_num : 0 < 2997),
    L2G.sendsB_eq hvA hvW hU.1 hU.2 (by norm_num : 2835 < 2997),
    elemOK_P hH.1 hH.2 h1 h2, elemOK_P hU.1 hU.2 h6 h7, h3, h4, h8, h9,
    plusB_P (p_comp hH.2 (p_comp hm hH.1)) (p_comp hH.2 (p_comp hxi hH.1)).2 h10,
    plusB_P (p_comp hU.2 (p_comp hm hU.1)) (p_comp hU.2 (p_comp hxi hU.1)).2 h11]
  rfl

theorem transOK_true : transOK = true := by
  unfold transOK
  rw [squareOK_of pX pXI.1 hEl_V kEl_V kSqV,
    squareOK_of pY pYI.1 hEl_V' kEl_V' kSqV']
  rfl

end CertificateChecks.KernelSpor.SuzRTG

end
