module

public import Certificates.Kernel.HNClsL.ChecksA
public import Certificates.Kernel.HNClsL.ChecksB
public import Certificates.Kernel.HNClsL.ChecksC
public import CFSG.Certificates.Kernel.HNClsLSound
public import Certificates.Kernel.SporSch.HN.PtCR
public import Certificates.Kernel.SporSch.HN.Pt2085
public import CFSG.Certificates.Kernel.J4Hub.Sound
public import CFSG.Certificates.Kernel.Spor.OrdCanon
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Asm
public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNOddCore.ThreeInvol
public import CFSG.Sporadic.HNOddCore.OuterFix

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelHNClsL

open CFSG.KS.Ord CFSG.KS.HNClsL CFSG.KC.HNClsL CFSG.KC.SlpPc
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore
open CertificateChecks.KernelSporSch.HNPt2103

local notation "OM" => ordMat 5 133 13 1729

section AbsModel

variable {G M : Type*} [Group G] [Monoid M]

@[expose] def CanM (C : ℕ → Prop) (f : ℕ → M) (m : G → M) (W : ℕ) : Prop := C W ∧ ∃ r : G, f W = m r

@[expose] noncomputable def evM (f : ℕ → M) (m : G → M) (W : ℕ) : G := by
  classical
  exact if h : ∃ r : G, f W = m r then Classical.choose h else 1

omit [Monoid M] in
theorem evM_spec {C : ℕ → Prop} {f : ℕ → M} {m : G → M} {W : ℕ} (h : CanM C f m W) :
    f W = m (evM f m W) := by
  unfold evM
  rw [dite_eq_left h.2]
  exact Classical.choose_spec h.2

omit [Monoid M] in
theorem evM_eq {C : ℕ → Prop} {f : ℕ → M} {m : G → M} (hm : Function.Injective m) {W : ℕ}
    {r : G} (hW : C W) (h : f W = m r) : CanM C f m W ∧ evM f m W = r :=
  ⟨⟨hW, r, h⟩, hm ((evM_spec (C := C) ⟨hW, r, h⟩).symm.trans h)⟩

theorem model_of {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {C : ℕ → Prop} {f : ℕ → M} {m : G → M}
    (hm : Function.Injective m) (hm1 : m 1 = 1) (hmm : ∀ r s, m (r * s) = m r * m s)
    (h1 : C ONE ∧ f ONE = 1)
    (hmul : ∀ {a b : ℕ}, C a → C b → C (mul a b) ∧ f (mul a b) = f a * f b)
    (hinj : ∀ {a b : ℕ}, C a → C b → f a = f b → a = b) :
    Model mul ONE (CanM C f m) (evM f m) := by
  refine ⟨evM_eq hm h1.1 (h1.2.trans hm1.symm), fun ha hb => ?_, fun ha hb he => ?_⟩
  · obtain ⟨hc, he⟩ := hmul ha.1 hb.1
    exact evM_eq hm hc (by rw [he, evM_spec ha, evM_spec hb, hmm])
  · exact hinj ha.1 hb.1 (by rw [evM_spec ha, evM_spec hb, he])

end AbsModel

section Model


theorem matR_injective : Function.Injective (matR : RH → Matrix (Fin 133) (Fin 133) (ZMod 5)) :=
  fun _ _ h => Subtype.ext (Units.ext h)

abbrev CanR : ℕ → Prop := CanM (Canon 5 133 13) OM matR

noncomputable abbrev evR : ℕ → RH := evM OM matR

theorem canon_inj {a b : ℕ} (ha : Canon 5 133 13 a) (hb : Canon 5 133 13 b) (h : OM a = OM b) :
    a = b :=
  CFSG.KS.J4Hub.ordMat_inj CFSG.KD.OrdHN.consts rfl
    (CFSG.KS.OrdCanon.validM_of_canon CFSG.KD.OrdHN.consts ha)
    (CFSG.KS.OrdCanon.validM_of_canon CFSG.KD.OrdHN.consts hb) h

theorem model : Model CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE CanR evR :=
  model_of matR_injective matR_one matR_mul
    ⟨(one_sound CFSG.KD.OrdHN.consts).1, CFSG.KS.SporSch.HNXP.one_ord⟩
    CFSG.KS.SporSch.HNXP.mm_sound canon_inj

theorem evR_eq {W : ℕ} {r : RH} (hW : Canon 5 133 13 W) (h : OM W = matR r) :
    CanR W ∧ evR W = r :=
  evM_eq matR_injective hW h

theorem finite_RH : Finite RH :=
  Finite.of_injective matR matR_injective

theorem lt_R {c : ℕ} (h : c < 36) : CFSG.KD.HNClsL.lt c = CFSG.KD.HNPt.R c := by
  unfold CFSG.KD.HNClsL.lt
  rw [blt_t h]

theorem lt_36 : CFSG.KD.HNClsL.lt 36 = CFSG.KD.HNPtC.GT 10 := rfl

theorem letter_lt {c : ℕ} (h : c < 36) : CanR (CFSG.KD.HNClsL.lt c) ∧
    evR (CFSG.KD.HNClsL.lt c) = jR (genJ c) := by
  rw [lt_R h]
  exact evR_eq (R_canon h) (by rw [R_mat h, matR_jR])

theorem letter_mem {c : ℕ} (hc : okC c = true) : CanR (CFSG.KD.HNClsL.lt c) ∧
    evR (CFSG.KD.HNClsL.lt c) = if c < 36 then jR (genJ c) else cR := by
  obtain ⟨h37, -⟩ := (okC_iff c).1 hc
  rcases Nat.lt_or_ge c 36 with h | h
  · rw [ite_eq_left h]
    exact letter_lt h
  · obtain rfl : c = 36 := by omega
    rw [ite_eq_right (by omega), lt_36]
    exact evR_eq (CertificateChecks.KernelSporSch.HNPtC.GT_canon (by norm_num))
      CertificateChecks.KernelSporSch.HNPtC.C_mat

theorem letter_J : ∀ c, okC c = true → c < 36 → evR (CFSG.KD.HNClsL.lt c) ∈ jR.range :=
  fun c hc h => by
    rw [(letter_mem hc).2, ite_eq_left h]
    exact ⟨_, rfl⟩

theorem lw_J : ∀ cs : List ℕ, (∀ c ∈ cs, c < 36) →
    lw (fun c => evR (CFSG.KD.HNClsL.lt c)) cs = jR (cs.map genJ).prod
  | [], _ => by simp [lw]
  | c :: cs, h => by
    have ih := lw_J cs fun c' h' => h c' (List.mem_cons_of_mem _ h')
    unfold lw at ih ⊢
    rw [List.map_cons, List.prod_cons, ih, (letter_lt (h c List.mem_cons_self)).2, List.map_cons,
      List.prod_cons, map_mul]

theorem baseA (c : ℕ) (h1 : okC c = true) : CanR (CFSG.KD.HNClsL.LMA c) ∧
    evR (CFSG.KD.HNClsL.LMA c) =
      lw (fun c => evR (CFSG.KD.HNClsL.lt c)) (CFSG.KD.HNClsL.EMA c) := by
  obtain ⟨h37, -⟩ := (okC_iff c).1 h1
  have e1 : CFSG.KD.HNClsL.LMA c = CFSG.KD.HNClsL.lt c := by
    unfold CFSG.KD.HNClsL.LMA
    rw [blt_t h37]
  have e2 : CFSG.KD.HNClsL.EMA c = [c] := by
    unfold CFSG.KD.HNClsL.EMA
    rw [blt_t h37]
  rw [e1, e2]
  refine ⟨(letter_mem h1).1, ?_⟩
  unfold lw
  rw [List.map_singleton, List.prod_singleton]

theorem macA (j : ℕ) : CanR (CFSG.KD.HNClsL.FA j) ∧ evR (CFSG.KD.HNClsL.FA j) =
    pw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolA j := by
  rcases Nat.lt_or_ge j 11 with hj | hj
  · obtain ⟨hg, hE⟩ := andB_trueH (CFSG.KD.HNClsL.mEA_all j hj)
    exact slp_pw model (L := CFSG.KD.HNClsL.LMA) (E := CFSG.KD.HNClsL.EMA)
      (RA := CFSG.KD.HNClsL.SA.RA) (RB := CFSG.KD.HNClsL.SA.RB) (n := 221) baseA
      CFSG.KD.HNClsL.rCA_all hg (beq_iff_eq.mp hE) (CFSG.KD.HNClsL.fW j hj)
  · have e1 : CFSG.KD.HNClsL.FA j = CFSG.KD.OrdHN.ONE := by
      change nthD CFSG.KD.OrdHN.ONE CFSG.KD.HNClsL.SA.PM j = _
      rw [nthD_eqH, List.getD_eq_default _ _ (by rw [CFSG.KD.HNClsL.pmA_length]; omega)]
    have e2 : nthD [] CFSG.KD.HNClsL.poolA j = [] := by
      rw [nthD_eqH, List.getD_eq_default _ _ (by rw [CFSG.KD.HNClsL.poolA_length]; omega)]
    unfold pw
    rw [e1, e2]
    refine ⟨model.one.1, ?_⟩
    rw [model.one.2]
    unfold lw
    rw [List.map_nil, List.prod_nil]

theorem rawA : Raw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolA CFSG.KD.HNClsL.gensA
    CFSG.KD.HNClsL.nQA CFSG.KD.HNClsL.linesA CFSG.KD.HNClsL.wlA :=
  raw_of_rest model (fun _ hc => (letter_mem hc).1) CFSG.KD.HNClsL.gAl
    CFSG.KD.HNClsL.gOk macA (fun j => by
      rw [← CFSG.KD.HNClsL.gGL]
      exact invW_ev model (fun _ hc => (letter_mem hc).1) CFSG.KD.HNClsL.gOk j)
    CFSG.KD.HNClsL.gR

theorem baseB (c : ℕ) (h1 : okC c = true) : CanR (CFSG.KD.HNClsL.ClsB.LM c) ∧
    evR (CFSG.KD.HNClsL.ClsB.LM c) =
      lw (fun c => evR (CFSG.KD.HNClsL.lt c)) (CFSG.KD.HNClsL.ClsB.EM c) := by
  obtain ⟨h37, -⟩ := (okC_iff c).1 h1
  have e1 : CFSG.KD.HNClsL.ClsB.LM c = CFSG.KD.HNClsL.lt c := by
    unfold CFSG.KD.HNClsL.ClsB.LM
    rw [blt_t h37]
  have e2 : CFSG.KD.HNClsL.ClsB.EM c = [c] := by
    unfold CFSG.KD.HNClsL.ClsB.EM
    rw [blt_t h37]
  rw [e1, e2]
  refine ⟨(letter_mem h1).1, ?_⟩
  unfold lw
  rw [List.map_singleton, List.prod_singleton]

theorem macB (j : ℕ) : CanR (CFSG.KD.HNClsL.ClsB.FA j) ∧ evR (CFSG.KD.HNClsL.ClsB.FA j) =
    pw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolB j := by
  rcases Nat.lt_or_ge j 9 with hj | hj
  · obtain ⟨hg, hE⟩ := andB_trueH (CFSG.KD.HNClsL.ClsB.mE_all j hj)
    exact slp_pw model (L := CFSG.KD.HNClsL.ClsB.LM) (E := CFSG.KD.HNClsL.ClsB.EM)
      (RA := CFSG.KD.HNClsL.SB.RA) (RB := CFSG.KD.HNClsL.SB.RB) (n := 419) baseB
      CFSG.KD.HNClsL.ClsB.rC_all hg (beq_iff_eq.mp hE) (CFSG.KD.HNClsL.ClsB.fW j hj)
  · have e1 : CFSG.KD.HNClsL.ClsB.FA j = CFSG.KD.OrdHN.ONE := by
      change nthD CFSG.KD.OrdHN.ONE CFSG.KD.HNClsL.SB.PM j = _
      rw [nthD_eqH, List.getD_eq_default _ _ (by rw [CFSG.KD.HNClsL.ClsB.pmB_length]; omega)]
    have e2 : nthD [] CFSG.KD.HNClsL.poolB j = [] := by
      rw [nthD_eqH, List.getD_eq_default _ _ (by rw [CFSG.KD.HNClsL.ClsB.poolB_length]; omega)]
    unfold pw
    rw [e1, e2]
    refine ⟨model.one.1, ?_⟩
    rw [model.one.2]
    unfold lw
    rw [List.map_nil, List.prod_nil]

theorem gGLB : (fun j => wordP CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE CFSG.KD.HNClsL.lt
    (invW (nthD List.nil CFSG.KD.HNClsL.poolB j))) = CFSG.KD.HNClsL.ClsB.GWU :=
  gRng_eq fun j h0 hj => by
    obtain ⟨hg, hE⟩ := andB_trueH (CFSG.KD.HNClsL.ClsB.gC_all j h0 hj).2.2
    have hs := slp_pw model (L := CFSG.KD.HNClsL.ClsB.LM) (E := CFSG.KD.HNClsL.ClsB.EM)
      (RA := CFSG.KD.HNClsL.SB.RA) (RB := CFSG.KD.HNClsL.SB.RB) (n := 419) baseB
      CFSG.KD.HNClsL.ClsB.rC_all hg
      ((beq_iff_eq.mp hE).trans ((invWA_eq _ _).trans (List.append_nil _)))
      (CFSG.KD.HNClsL.ClsB.gW j h0 hj)
    have hi := invW_ev model (fun _ hc => (letter_mem hc).1) CFSG.KD.HNClsL.ClsB.gOk j
    exact model.inj hi.1 hs.1 (hi.2.trans hs.2.symm)

theorem rawB : Raw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolB CFSG.KD.HNClsL.gensB
    CFSG.KD.HNClsL.nQB CFSG.KD.HNClsL.linesB CFSG.KD.HNClsL.wlB :=
  raw_of_rest model (fun _ hc => (letter_mem hc).1) CFSG.KD.HNClsL.ClsB.gAl
    CFSG.KD.HNClsL.ClsB.gOk macB (fun j => by
      rw [← gGLB]
      exact invW_ev model (fun _ hc => (letter_mem hc).1) CFSG.KD.HNClsL.ClsB.gOk j)
    CFSG.KD.HNClsL.ClsB.gR

theorem baseC (c : ℕ) (h1 : okC c = true) : CanR (CFSG.KD.HNClsL.ClsC.LM c) ∧
    evR (CFSG.KD.HNClsL.ClsC.LM c) =
      lw (fun c => evR (CFSG.KD.HNClsL.lt c)) (CFSG.KD.HNClsL.ClsC.EM c) := by
  obtain ⟨h37, -⟩ := (okC_iff c).1 h1
  have e1 : CFSG.KD.HNClsL.ClsC.LM c = CFSG.KD.HNClsL.lt c := by
    unfold CFSG.KD.HNClsL.ClsC.LM
    rw [blt_t h37]
  have e2 : CFSG.KD.HNClsL.ClsC.EM c = [c] := by
    unfold CFSG.KD.HNClsL.ClsC.EM
    rw [blt_t h37]
  rw [e1, e2]
  refine ⟨(letter_mem h1).1, ?_⟩
  unfold lw
  rw [List.map_singleton, List.prod_singleton]

theorem macC (j : ℕ) : CanR (CFSG.KD.HNClsL.ClsC.FA j) ∧ evR (CFSG.KD.HNClsL.ClsC.FA j) =
    pw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolC j := by
  rcases Nat.lt_or_ge j 13 with hj | hj
  · obtain ⟨hg, hE⟩ := andB_trueH (CFSG.KD.HNClsL.ClsC.mE_all j hj)
    exact slp_pw model (L := CFSG.KD.HNClsL.ClsC.LM) (E := CFSG.KD.HNClsL.ClsC.EM)
      (RA := CFSG.KD.HNClsL.SC.RA) (RB := CFSG.KD.HNClsL.SC.RB) (n := 131) baseC
      CFSG.KD.HNClsL.ClsC.rC_all hg (beq_iff_eq.mp hE) (CFSG.KD.HNClsL.ClsC.fW j hj)
  · have e1 : CFSG.KD.HNClsL.ClsC.FA j = CFSG.KD.OrdHN.ONE := by
      change nthD CFSG.KD.OrdHN.ONE CFSG.KD.HNClsL.SC.PM j = _
      rw [nthD_eqH, List.getD_eq_default _ _ (by rw [CFSG.KD.HNClsL.ClsC.pmC_length]; omega)]
    have e2 : nthD [] CFSG.KD.HNClsL.poolC j = [] := by
      rw [nthD_eqH, List.getD_eq_default _ _ (by rw [CFSG.KD.HNClsL.ClsC.poolC_length]; omega)]
    unfold pw
    rw [e1, e2]
    refine ⟨model.one.1, ?_⟩
    rw [model.one.2]
    unfold lw
    rw [List.map_nil, List.prod_nil]

theorem gGLC : (fun j => wordP CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE CFSG.KD.HNClsL.lt
    (invW (nthD List.nil CFSG.KD.HNClsL.poolC j))) = CFSG.KD.HNClsL.ClsC.GWU :=
  gRng_eq fun j h0 hj => by
    obtain ⟨hg, hE⟩ := andB_trueH (CFSG.KD.HNClsL.ClsC.gC_all j h0 hj).2.2
    have hs := slp_pw model (L := CFSG.KD.HNClsL.ClsC.LM) (E := CFSG.KD.HNClsL.ClsC.EM)
      (RA := CFSG.KD.HNClsL.SC.RA) (RB := CFSG.KD.HNClsL.SC.RB) (n := 131) baseC
      CFSG.KD.HNClsL.ClsC.rC_all hg
      ((beq_iff_eq.mp hE).trans ((invWA_eq _ _).trans (List.append_nil _)))
      (CFSG.KD.HNClsL.ClsC.gW j h0 hj)
    have hi := invW_ev model (fun _ hc => (letter_mem hc).1) CFSG.KD.HNClsL.ClsC.gOk j
    exact model.inj hi.1 hs.1 (hi.2.trans hs.2.symm)

theorem rawC : Raw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolC CFSG.KD.HNClsL.gensC
    CFSG.KD.HNClsL.nQC CFSG.KD.HNClsL.linesC CFSG.KD.HNClsL.wlC :=
  raw_of_rest model (fun _ hc => (letter_mem hc).1) CFSG.KD.HNClsL.ClsC.gAl
    CFSG.KD.HNClsL.ClsC.gOk macC (fun j => by
      rw [← gGLC]
      exact invW_ev model (fun _ hc => (letter_mem hc).1) CFSG.KD.HNClsL.ClsC.gOk j)
    CFSG.KD.HNClsL.ClsC.gR

end Model

section AbsPull

variable {R J : Type*} [Group R] [Group J] (j : J →* R)

@[expose] noncomputable def preJ (r : R) : J := by
  classical
  exact if h : r ∈ j.range then Classical.choose (MonoidHom.mem_range.1 h) else 1

theorem j_preJ {r : R} (h : r ∈ j.range) : j (preJ j r) = r := by
  unfold preJ
  rw [dite_eq_left h]
  exact Classical.choose_spec (MonoidHom.mem_range.1 h)

theorem prod_conj_preJ (φ : R →* MulAut J) (hφ : ∀ g, φ (j g) = MulAut.conj g) (y : R) :
    ∀ l : List R, (∀ k ∈ l, k ∈ j.range) →
    ((l.map (preJ j)).map fun k => MulAut.conj k * φ y * (MulAut.conj k)⁻¹).prod =
      φ ((l.map fun k => k * y * k⁻¹).prod)
  | [], _ => by simp
  | k :: l, h => by
    rw [List.map_cons, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      prod_conj_preJ φ hφ y l fun k' h' => h k' (List.mem_cons_of_mem _ h'), map_mul, map_mul,
      map_mul, map_inv, ← hφ, j_preJ j (h k List.mem_cons_self)]

variable {j} (hj : Function.Injective j)
include hj

theorem pull_card {Q : Subgroup R} (hQK : Q ≤ j.range) : Nat.card (Q.comap j) = Nat.card Q := by
  rw [← Subgroup.card_map_of_injective hj, Subgroup.map_comap_eq_self hQK]

theorem zpowers_pull {a b : J} (h : Subgroup.zpowers (j a) = Subgroup.zpowers (j b)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply Subgroup.map_injective hj
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact h

theorem pull_cover {y : R} {Q : Subgroup R} {xs : ℕ → R} {n : ℕ} (hxs : ∀ i, xs i ∈ j.range)
    (hcov : ∀ z ∈ Q, orderOf z = 5 → ∃ i < n, ∃ g ∈ j.range, g * y = y * g ∧
      Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) :
    ∀ z ∈ Q.comap j, orderOf z = 5 → ∃ i < n, ∃ g : J, j g * y = y * j g ∧
      Subgroup.zpowers z = Subgroup.zpowers (g * preJ j (xs i) * g⁻¹) := by
  intro z hz hzo
  have hz' : j z ∈ Q := Subgroup.mem_comap.1 hz
  have hzo' : orderOf (j z) = 5 := (orderOf_injective j hj z).trans hzo
  obtain ⟨i, hi, g, hg, hgc, hzg⟩ := hcov (j z) hz' hzo'
  refine ⟨i, hi, preJ j g, ?_, ?_⟩
  · rw [j_preJ j hg]
    exact hgc
  · refine zpowers_pull hj ?_
    rw [map_mul, map_mul, map_inv, j_preJ j hg, j_preJ j (hxs i)]
    exact hzg

theorem pull_wit {φ : R →* MulAut J} (hφ : ∀ g, φ (j g) = MulAut.conj g)
    (hφi : Function.Injective φ) {y : R} {xs : ℕ → R} {n : ℕ} (hxs : ∀ i, xs i ∈ j.range)
    (hwit : ∀ i < n, ∃ l : List R, (∀ k ∈ l, k ∈ j.range ∧ k * xs i = xs i * k) ∧
      5 ∣ orderOf ((l.map fun k => k * y * k⁻¹).prod)) :
    ∀ i < n, ∃ l : List J, (∀ k ∈ l, k * preJ j (xs i) = preJ j (xs i) * k) ∧
      5 ∣ orderOf ((l.map fun k => MulAut.conj k * φ y * (MulAut.conj k)⁻¹).prod) := by
  intro i hi
  obtain ⟨l, hl, h5⟩ := hwit i hi
  refine ⟨l.map (preJ j), ?_, ?_⟩
  · intro k hk
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
    apply hj
    rw [map_mul, map_mul, j_preJ j (hl k' hk').1, j_preJ j (hxs i)]
    exact (hl k' hk').2
  · rw [prod_conj_preJ j φ hφ _ l fun k hk => (hl k hk).1, orderOf_injective φ hφi]
    exact h5

theorem facts_pull [Finite R] [j.range.Normal] {φ : R →* MulAut J}
    (hφ : ∀ g, φ (j g) = MulAut.conj g) (hφi : Function.Injective φ) {lt : ℕ → R}
    (hK : ∀ c, okC c = true → c < 36 → lt c ∈ j.range) {pool : List (List ℕ)} {gens : List ℕ}
    {nQ : ℕ} {lines wl : List (List (ℕ × ℕ))} (hr : Raw lt pool gens nQ lines wl) {y : R}
    (hy : pw lt pool 0 = y) :
    ∃ (Q : Subgroup J) (xs : ℕ → J),
      (∀ q ∈ Q, j q * y = y * j q) ∧ Nat.card Q = nQ ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < wl.length, ∃ g : J, j g * y = y * j g ∧
          Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < wl.length, ∃ l : List J, (∀ k ∈ l, k * xs i = xs i * k) ∧
          5 ∣ orderOf ((l.map fun k => MulAut.conj k * φ y * (MulAut.conj k)⁻¹).prod)) := by
  obtain ⟨Q, xs, hQK, hxs, hcomm, hcard, hcov, hwit⟩ := facts_of_raw j.range hK hr
  rw [hy] at hcomm hcov hwit
  refine ⟨Q.comap j, fun i => preJ j (xs i), fun q hq => hcomm _ (Subgroup.mem_comap.1 hq), ?_,
    pull_cover hj hxs hcov, pull_wit hj hφ hφi hxs hwit⟩
  rw [pull_card hj hQK, hcard]

end AbsPull

section Facts


theorem facts_HN {pool : List (List ℕ)} {gens : List ℕ} {nQ : ℕ}
    {lines wl : List (List (ℕ × ℕ))}
    (hr : Raw (fun c => evR (CFSG.KD.HNClsL.lt c)) pool gens nQ lines wl) {y : RH}
    (hy : pw (fun c => evR (CFSG.KD.HNClsL.lt c)) pool 0 = y) :
    ∃ (Q : Subgroup JH) (xs : ℕ → JH),
      (∀ q ∈ Q, jR q * y = y * jR q) ∧ Nat.card Q = nQ ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < wl.length, ∃ g : JH, jR g * y = y * jR g ∧
          Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < wl.length, ∃ l : List JH, (∀ k ∈ l, k * xs i = xs i * k) ∧
          5 ∣ orderOf ((l.map fun k => MulAut.conj k * conjR y * (MulAut.conj k)⁻¹).prod)) := by
  have : (jR.range : Subgroup RH).Normal := range_jR_normal
  have : Finite RH := finite_RH
  exact facts_pull jR_injective conjR_jR conjR_injective letter_J hr hy

end Facts

theorem poolA0 : nthD [] CFSG.KD.HNClsL.poolA 0 = [0] := by decide +kernel

theorem poolB0 : nthD [] CFSG.KD.HNClsL.poolB 0 = CFSG.KD.HNPtC.t4c := by decide +kernel

theorem poolC0 : nthD [] CFSG.KD.HNClsL.poolC 0 = [36] := by decide +kernel

theorem sizes : CFSG.KD.HNClsL.nQA = 125 ∧ CFSG.KD.HNClsL.wlA.length = 7 ∧
    CFSG.KD.HNClsL.nQB = 25 ∧ CFSG.KD.HNClsL.wlB.length = 5 ∧
    CFSG.KD.HNClsL.nQC = 25 ∧ CFSG.KD.HNClsL.wlC.length = 3 := by
  decide +kernel

theorem yA :
    pw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolA 0 = jR aJ := by
  unfold pw
  rw [poolA0, lw_J [0] (by simp), List.map_singleton, List.prod_singleton, genJ, ite_eq_left (by omega),
    CertificateChecks.KernelSporSch.HNPt2085.sL_eq_hJ 0 (by omega), hJ_zero, h1J_eq_aJ]

theorem yB :
    pw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolB 0 = jR t4J := by
  unfold pw
  have hl := CertificateChecks.KernelSporSch.HNPtC.letters_c4.2.2.2.2
  rw [poolB0, lw_J _ CertificateChecks.KernelSporSch.HNPtC.codes_c4.2.2.2.2,
    CertificateChecks.KernelSporSch.HNPtC.codes_c4.2.2.1, prod_scode _ hl,
    CertificateChecks.KernelSporSch.HNPt2085.wJ_sL _ hl, t4J_eq]

theorem yC :
    pw (fun c => evR (CFSG.KD.HNClsL.lt c)) CFSG.KD.HNClsL.poolC 0 = t1R := by
  unfold pw lw
  rw [poolC0, List.map_singleton, List.prod_singleton, (letter_mem (c := 36) rfl).2,
    ite_eq_right (by omega), t1R_eq]

theorem factsA :
    ∃ (Q : Subgroup JH) (xs : ℕ → JH),
      (∀ q ∈ Q, jR q * jR aJ = jR aJ * jR q) ∧ Nat.card Q = 125 ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < 7, ∃ g : JH, jR g * jR aJ = jR aJ * jR g ∧
          Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < 7, ∃ l : List JH, (∀ k ∈ l, k * xs i = xs i * k) ∧
          5 ∣ orderOf ((l.map fun k => MulAut.conj k * conjR (jR aJ) * (MulAut.conj k)⁻¹).prod)) := by
  have h := facts_HN rawA yA
  rwa [sizes.1, sizes.2.1] at h

theorem factsB :
    ∃ (Q : Subgroup JH) (xs : ℕ → JH),
      (∀ q ∈ Q, jR q * jR t4J = jR t4J * jR q) ∧ Nat.card Q = 25 ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < 5, ∃ g : JH, jR g * jR t4J = jR t4J * jR g ∧
          Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < 5, ∃ l : List JH, (∀ k ∈ l, k * xs i = xs i * k) ∧
          5 ∣ orderOf ((l.map fun k => MulAut.conj k * conjR (jR t4J) * (MulAut.conj k)⁻¹).prod)) := by
  have h := facts_HN rawB yB
  rwa [sizes.2.2.1, sizes.2.2.2.1] at h

theorem factsC :
    ∃ (Q : Subgroup JH) (xs : ℕ → JH),
      (∀ q ∈ Q, jR q * t1R = t1R * jR q) ∧ Nat.card Q = 25 ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < 3, ∃ g : JH, jR g * t1R = t1R * jR g ∧
          Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < 3, ∃ l : List JH, (∀ k ∈ l, k * xs i = xs i * k) ∧
          5 ∣ orderOf ((l.map fun k => MulAut.conj k * conjR t1R * (MulAut.conj k)⁻¹).prod)) := by
  have h := facts_HN rawC yC
  rwa [sizes.2.2.2.2.1, sizes.2.2.2.2.2] at h

end CertificateChecks.KernelHNClsL

end
