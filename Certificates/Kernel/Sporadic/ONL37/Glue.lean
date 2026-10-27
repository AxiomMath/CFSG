module

public import Certificates.Kernel.Sporadic.ONL37.Defs
public import Certificates.Kernel.Sporadic.ONC.Chain
public import Certificates.Kernel.Sporadic.ON2.Assemble
public import CFSG.Certificates.Kernel.Spor.ONCSOpSound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelToJ
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenNamed
public import CFSG.Sporadic.ON.Action
public import CFSG.RankThree.Native.ONTripleSigBase
import Certificates.Kernel.Sporadic.ONL37.W0
import Certificates.Kernel.Sporadic.ONL37.W1
import Certificates.Kernel.Sporadic.ONL37.W2
import Certificates.Kernel.Sporadic.ONL37.Prog
import Certificates.Kernel.Sporadic.ONL37.Fix
import all CFSG.Sporadic.Bridge.Common
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Recognition.CoverChainSub

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.ONL37

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONC CFSG.KS.Words CFSG.RankThree.Native.ONTriple
open CFSG.KD.ONL37 CertificateChecks.KernelSpor.ONC CFSG.Sporadic.ON.Native
open CFSG.Sporadic.Th (Rep idx idx_of_lt)
open scoped Matrix

section SLP

variable {X Y : Type*} [Group X] [Group Y]

theorem getD_map_hom (f : X →* Y) (R : Array X) (k : ℕ) : (R.map f).getD k 1 = f (R.getD k 1) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases R[k]? <;> simp

theorem wordG_map_hom (f : X →* Y) (R : Array X) (w : List (ℕ × Bool)) :
    wordG (R.map f) w = f (wordG R w) := by
  unfold wordG
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, getD_map_hom]
  split <;> simp

theorem stepG_map_hom (f : X →* Y) (R : Array X) (o : SOp) :
    stepG (R.map f) o = (stepG R o).map f := by
  cases o with
  | word w =>
    simp only [stepG]
    rw [Array.map_push, wordG_map_hom]
  | pow e i =>
    simp only [stepG]
    rw [Array.map_push, getD_map_hom, map_pow]

theorem runG_map_hom (f : X →* Y) : ∀ (prog : List SOp) (R : Array X),
    runG (R.map f) prog = (runG R prog).map f
  | [], R => rfl
  | o :: prog, R => by
    simp only [runG, List.foldl_cons] at *
    rw [stepG_map_hom]
    exact runG_map_hom f prog (stepG R o)

end SLP

theorem pv_FA : ∀ c < 154, PV (FA c) := fun c hc =>
  pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsAK2
    (CertificateChecks.KernelSpor.ON.list_eq ONW.LA ONW.CA
      (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listA2)) c hc)

theorem pv_FB : ∀ c < 154, PV (FB c) := fun c hc =>
  pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsBK2
    (CertificateChecks.KernelSpor.ON.list_eq ONW.LB ONW.CB
      (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listB2)) c hc)

theorem reps_ga : Reps matHom (batK CS DS FA 0 154) ga0 := batK_reps pv_FA colA

theorem reps_gb : Reps matHom (batK CS DS FB 0 154) gb0 := batK_reps pv_FB colB

theorem chunk_ok {c : ℕ} (hc : c < 8) : l37Wch c = true := by
  interval_cases c
  exacts [l37Wch0, l37Wch1, l37Wch2, l37Wch3, l37Wch4, l37Wch5, l37Wch6, l37Wch7]

theorem chunk_step {c : ℕ} (hc : c < 8) {x : J0} (hpre : Reps matHom (preC c) x) :
    Reps matHom (ipC c) (x * CFSG.Sporadic.Th.wordG genG0 (chunkW c)) :=
  chunkK_sound (chunk_ok hc) reps_ga reps_gb hpre

theorem fix_parts : ckOK = true ∧ ∀ k < 9, fixK k = true := by
  have h := l37Fix_ok
  unfold l37Fix at h
  rw [bAnd_iff', bAnd_iff', bAnd_iff'] at h
  exact ⟨h.1, allN_spec' h.2.2.2⟩

theorem ck_parts : (∀ c < 8, ckA c = 0 ∨
      (0 < c ∧ ckW (c - 1) = ckW c ∧ ckA (c - 1) + ckB (c - 1) = ckA c)) ∧
    ∀ k < 7, imgIdx.getD k 0 < 8 ∧ ckW (imgIdx.getD k 0) = k ∧
      ckA (imgIdx.getD k 0) + ckB (imgIdx.getD k 0) = IMW.WL k := by
  have h := fix_parts.1
  unfold ckOK at h
  rw [bAnd_iff', bAnd_iff', bAnd_iff'] at h
  obtain ⟨-, -, h1, h2⟩ := h
  refine ⟨fun c hc => ?_, fun k hk => ?_⟩
  · have h3 := allN_spec' h1 c hc
    cases e : Nat.beq (ckA c) 0
    · rw [e] at h3
      dsimp only at h3
      rw [bAnd_iff', bAnd_iff'] at h3
      exact Or.inr ⟨Nat.blt_eq.mp h3.1, Nat.eq_of_beq_eq_true h3.2.1,
        Nat.eq_of_beq_eq_true h3.2.2⟩
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · have h3 := allN_spec' h2 k hk
    rw [strictB_eq', bAnd_iff', bAnd_iff'] at h3
    exact ⟨Nat.blt_eq.mp h3.1, Nat.eq_of_beq_eq_true h3.2.1, Nat.eq_of_beq_eq_true h3.2.2⟩

theorem wordG_append (g : ℤ → J0) (a b : List ℤ) :
    CFSG.Sporadic.Th.wordG g (a ++ b) =
      CFSG.Sporadic.Th.wordG g a * CFSG.Sporadic.Th.wordG g b := by
  unfold CFSG.Sporadic.Th.wordG
  rw [List.map_append, List.prod_append]

theorem chunk_reps : ∀ c < 8,
    Reps matHom (ipC c) (CFSG.Sporadic.Th.wordG genG0 ((imgW (ckW c)).take (ckA c + ckB c))) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    by_cases h0 : ckA c = 0
    · have hpre : preC c = ONE := by
        unfold preC
        rw [h0]
        rfl
      have h := chunk_step hc (x := 1) (by rw [hpre]; exact reps_one)
      rw [one_mul] at h
      have e : chunkW c = (imgW (ckW c)).take (ckA c + ckB c) := by
        unfold chunkW
        rw [h0, List.drop_zero, Nat.zero_add]
      rwa [← e]
    · obtain ⟨hpos, hw, ha⟩ := (ck_parts.1 c hc).resolve_left h0
      have hne : Nat.beq (ckA c) 0 = false := by
        cases e : Nat.beq (ckA c) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) h0
      have hpre : preC c = ipC (c - 1) := by
        unfold preC
        rw [hne]
        rfl
      have h := chunk_step hc (by rw [hpre]; exact ih (c - 1) (by omega) (by omega))
      rw [hw, ha] at h
      unfold chunkW at h
      rw [← wordG_append, ← List.take_add] at h
      exact h

theorem length_decW (W : Nat) : ∀ L, (decW W L).length = L
  | 0 => rfl
  | L + 1 => by rw [decW, List.length_cons, length_decW W L]

theorem imgWords_get {k : ℕ} (hk : k < 7) :
    (CFSG.Sporadic.Bridge.ONGPL.Native.imgWords ())[k]! = imgW k := by
  rw [CertificateChecks.KernelSpor.ON2.img_words,
    getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]
  rfl

theorem img_reps {k : ℕ} (hk : k < 7) : Reps matHom (imgL k) (img0 k) := by
  obtain ⟨hc, hw, hab⟩ := ck_parts.2 k hk
  have h := chunk_reps _ hc
  have hl : (imgW k).length = IMW.WL k := length_decW _ _
  rw [hw, hab, List.take_of_length_le (le_of_eq hl)] at h
  have e : img0 k = CFSG.Sporadic.Th.wordG genG0 (imgW k) := by
    unfold img0
    rw [← imgWords_get hk]
  rw [e]
  exact h

@[expose] noncomputable def gJ0 : Array J0 :=
  Array.ofFn fun k : Fin 8 => if k.val < 7 then img0 k.val else 1

noncomputable abbrev g0r (r : ℕ) : J0 := (runG gJ0 progM).getD r 1

theorem gJ0_getD {r : ℕ} (hr : r < 8) : gJ0.getD r 1 = if r < 7 then img0 r else 1 := by
  simp [gJ0, Array.getD_eq_getD_getElem?, hr]

theorem initL_getD {r : ℕ} (hr : r < 8) : initL.getD r 0 = if r < 7 then imgL r else ONE := by
  interval_cases r <;> rfl

theorem init_reps : ∀ r < initL.length, Reps matHom (initL.getD r 0) (gJ0.getD r 1) := by
  intro r hr
  have hr8 : r < 8 := hr
  rw [initL_getD hr8, gJ0_getD hr8]
  split_ifs with h7
  · exact img_reps h7
  · exact reps_one

theorem progM_lt : sopLt 8 progM = true := by decide

theorem prog_facts : ∃ st : List Nat × Bool, finL st = true ∧ (st.2 = true →
    st.1.length = initL.length + progM.length ∧ ∀ r < st.1.length,
      Reps matHom (st.1.getD r 0) (g0r r) ∧ (VIf r ≠ 0 → Reps matHom (VIf r) (g0r r)⁻¹)) :=
  sopK_sound (init := initL) (VI := VIf) (fin := finL) (prog := progM) (g := gJ0) l37Prog_ok
    progM_lt (by rw [gJ0, Array.size_ofFn]; rfl) init_reps

theorem ML_reps {q : ℕ} (hq : q < 12) (hn : regL (q / 6) < 200)
    (hv : regV (q % 6 / 2) (q % 2) < 200) :
    Reps matHom (MLf q) ((g0r (regL (q / 6)))⁻¹ * g0r (regV (q % 6 / 2) (q % 2)) *
      g0r (regL (q / 6))) := by
  obtain ⟨st, hfin, hinv⟩ := prog_facts
  unfold finL at hfin
  simp only [strictB_eq'] at hfin
  rw [bAnd_iff', bAnd_iff'] at hfin
  obtain ⟨hok, hlen, hall⟩ := hfin
  obtain ⟨-, hR⟩ := hinv hok
  have hlen' : st.1.length = 200 := Nat.eq_of_beq_eq_true hlen
  have h := allN_spec' hall q hq
  rw [bAnd_iff'] at h
  obtain ⟨hv0, he⟩ := h
  have hVI : VIf (regL (q / 6)) ≠ 0 := by
    intro h0
    have h1 : Nat.beq (VIf (regL (q / 6))) 0 = false := notB_true hv0
    rw [h0] at h1
    exact absurd h1 (by decide)
  obtain ⟨hNr, hNi⟩ := hR _ (by rw [hlen']; exact hn)
  have hVr := (hR _ (by rw [hlen']; exact hv)).1
  rw [← Nat.eq_of_beq_eq_true he]
  exact reps_mul (reps_mul (hNi hVI) hVr) hNr

local notation "rowAt" => CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven.rowAt

theorem gi_facts : ∀ k < 9, ∀ j < 4, GI.getD (4 * k + j) 0 / 6 = j / 2 ∧
    GI.getD (4 * k + j) 0 % 6 / 2 = rowAt 0 k (j / 2) ∧ GI.getD (4 * k + j) 0 % 2 = j % 2 ∧
    GI.getD (4 * k + j) 0 < 12 ∧ regL (j / 2) < 200 ∧ regV (rowAt 0 k (j / 2)) (j % 2) < 200 := by
  decide

theorem fix_pt {k : ℕ} (hk : k < 9) : W.getD k 0 < 245520 ∧ ∀ j < 4,
    CFSG.KS.Ord.Canon 3 154 11 (MLf (GI.getD (4 * k + j) 0)) →
      omat (MLf (GI.getD (4 * k + j) 0)) *ᵥ vecK (key ONW.K (W.getD k 0)) =
        vecK (key ONW.K (W.getD k 0)) := by
  have h := fix_parts.2 k hk
  unfold fixK at h
  simp only [strictB_eq'] at h
  rw [bAnd_iff', bAnd_iff'] at h
  obtain ⟨hlt, hcan, hall⟩ := h
  refine ⟨Nat.blt_eq.mp hlt, fun j hj hM => ?_⟩
  have hF : ∀ c < 1, PV ((fun _ => key ONW.K (W.getD k 0)) (0 + c)) :=
    fun _ _ => pv_of_canon hcan
  have hX := batK_canon (F := fun _ => key ONW.K (W.getD k 0)) (lo := 0) (cnt := 1) (by norm_num) hF
  have e : mul3 LL HH CM RM (MLf (GI.getD (4 * k + j) 0))
      (batK CS DS (fun _ => key ONW.K (W.getD k 0)) 0 1) =
        batK CS DS (fun _ => key ONW.K (W.getD k 0)) 0 1 :=
    Nat.eq_of_beq_eq_true (allN_spec' hall j hj)
  have hm := (mul3_sound hM hX).2
  rw [e] at hm
  have hcol : ∀ s : Fin 154,
      omat (batK CS DS (fun _ => key ONW.K (W.getD k 0)) 0 1) s ⟨0, by norm_num⟩ =
        vecK (key ONW.K (W.getD k 0)) s := fun s => by
    rw [batK_omat (by norm_num) hF, if_pos (by norm_num)]
  funext r
  have hrc := congrFun (congrFun hm r) ⟨0, by norm_num⟩
  rw [Matrix.mul_apply] at hrc
  have hv : (omat (MLf (GI.getD (4 * k + j) 0)) *ᵥ vecK (key ONW.K (W.getD k 0))) r =
      ∑ s, omat (MLf (GI.getD (4 * k + j) 0)) r s *
        omat (batK CS DS (fun _ => key ONW.K (W.getD k 0)) 0 1) s ⟨0, by norm_num⟩ := by
    simp only [Matrix.mulVec, dotProduct, hcol]
  rw [hv, ← hrc, hcol r]

noncomputable abbrev x0 (k j : ℕ) : J0 :=
  (g0r (regL (j / 2)))⁻¹ * g0r (regV (rowAt 0 k (j / 2)) (j % 2)) * g0r (regL (j / 2))

theorem x0_fix {k : ℕ} (hk : k < 9) : W.getD k 0 < nPts ∧ ∀ j < 4,
    idx nPts (x0 k j) (W.getD k 0) = W.getD k 0 := by
  obtain ⟨hw, hfix⟩ := fix_pt hk
  refine ⟨hw, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gi_facts k hk j hj
  have hR := ML_reps h4 (by rw [h1]; exact h5) (by rw [h2, h3]; exact h6)
  rw [h1, h2, h3] at hR
  have hm := hfix j hj hR.1
  rw [hR.2, matHom_apply] at hm
  rw [x0]
  apply (idx_eq_iff0 hw hw).2
  rw [smul_vec0, P_key hw]
  exact hm

section Bridge

open CFSG.Sporadic.ON (J)
open CFSG.Sporadic.Bridge.ON (img rep_img)


@[expose] noncomputable def gJ : Array J :=
  Array.ofFn fun k : Fin 8 => if k.val < 7 then img k.val else 1

theorem perm_eq {T : CFSG.Sporadic.Th.Native.Table} {g : J} {h : J0} (hg : Rep nPts T g)
    (hh : Rep nPts T h) :
    MulAction.toPermHom J (Fin nPts) g = MulAction.toPermHom J0 (Fin nPts) h := by
  refine Equiv.ext fun x => ?_
  obtain ⟨i, hi⟩ := x
  apply Fin.ext
  rw [MulAction.toPermHom_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    MulAction.toPerm_apply, ← idx_of_lt g hi, ← idx_of_lt h hi, ← hg i hi, hh i hi]

theorem gJ_map : gJ.map (MulAction.toPermHom J (Fin nPts)) =
    gJ0.map (MulAction.toPermHom J0 (Fin nPts)) := by
  apply Array.ext
  · simp [gJ, gJ0]
  · intro i h1 h2
    simp only [gJ, gJ0, Array.getElem_map, Array.getElem_ofFn]
    split_ifs with h7
    · exact perm_eq (rep_img h7) (rep_img0 h7)
    · simp

theorem perm_reg (r : ℕ) : MulAction.toPermHom J (Fin nPts) ((runG gJ progM).getD r 1) =
    MulAction.toPermHom J0 (Fin nPts) (g0r r) := by
  rw [g0r, ← getD_map_hom, ← getD_map_hom, ← runG_map_hom, ← runG_map_hom, gJ_map]

end Bridge

section Model

open CFSG.Sporadic.ON (J)
open CFSG.Sporadic.Bridge.ON (img toJ)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven (xE lY rRegL rRegV)


@[expose] noncomputable def gGM : Array GM := Array.ofFn fun k : Fin 8 => ⟨gM k, gM_mem k⟩

theorem gGM_map_subtype : gGM.map M.subtype = gMArr := by
  unfold gGM gMArr
  rw [Array.map_ofFn]
  rfl

theorem eM_eq_runG (r : ℕ) : (⟨eM r, eM_mem r⟩ : GM) = (runG gGM progM).getD r 1 := by
  apply Subtype.ext
  have h := getD_map_hom M.subtype (runG gGM progM) r
  rw [← runG_map_hom, gGM_map_subtype] at h
  have h3 : eM r = (runG gMArr progM).getD r 1 := by
    unfold eM regM
    rfl
  change eM r = ((runG gGM progM).getD r 1).val
  rw [h3, h, Subgroup.coe_subtype]

theorem phiJ_gGM (k : Fin 8) :
    phiJ (⟨gM k, gM_mem k⟩ : GM) = if k.val < 7 then img k.val else 1 := by
  have e : (⟨gM k, gM_mem k⟩ : GM) = modelEquiv (PresentedGroup.of k) := by
    apply Subtype.ext
    rw [modelEquiv_apply, psiM_of]
  rw [e, phiJ_of, piON_of]
  split_ifs with hk
  · have hk' : k.val < PON.generatorCount := by rw [generatorCount_PON]; exact hk
    have hp : pGen PON k.val = CFSG.Sporadic.Bridge.presGen PON k.val := by
      unfold pGen CFSG.Sporadic.Bridge.presGen
      rfl
    rw [hp]
    exact CFSG.Sporadic.Bridge.presHom_presGen _ _ _ hk'
  · have h7 : k.val = 7 := by have := k.isLt; omega
    rw [h7, pGen_seven, map_one]

theorem gGM_map_phiJ : gGM.map phiJ = gJ := by
  apply Array.ext
  · simp only [gGM, gJ, Array.size_map, Array.size_ofFn]
  · intro i h1 h2
    simp only [gGM, gJ, Array.getElem_map, Array.getElem_ofFn]
    exact phiJ_gGM ⟨i, by simpa only [gGM, Array.size_map, Array.size_ofFn] using h1⟩

theorem phiJ_eM (r : ℕ) : phiJ (⟨eM r, eM_mem r⟩ : GM) = (runG gJ progM).getD r 1 := by
  rw [eM_eq_runG, ← getD_map_hom, ← runG_map_hom, gGM_map_phiJ]


theorem perm_lY {k : ℕ} (j : Fin 4) :
    MulAction.toPermHom J (Fin nPts) (phiJ (lY 0 k j)) =
      MulAction.toPermHom J0 (Fin nPts) (x0 k j.val) := by
  have hl : j.val / 2 < 4 := by omega
  have e1 : lY 0 k j = xE 0 (j.val / 2) (rowAt 0 k (j.val / 2)) (j.val % 2) := by
    fin_cases j <;> rfl
  have hn : CFSG.RankThree.Native.ONTriple.nL 0 (j.val / 2) =
      (⟨eM (rRegL 0 (j.val / 2)), eM_mem _⟩ : GM) := Subtype.ext (eM_rL (by norm_num) hl).symm
  have e2 : xE 0 (j.val / 2) (rowAt 0 k (j.val / 2)) (j.val % 2) =
      (⟨eM (rRegL 0 (j.val / 2)), eM_mem _⟩ : GM)⁻¹ *
        (⟨eM (rRegV 0 (rowAt 0 k (j.val / 2)) (j.val % 2)), eM_mem _⟩ : GM) *
        (⟨eM (rRegL 0 (j.val / 2)), eM_mem _⟩ : GM) := by
    unfold xE
    rw [hn]
    rfl
  have hL : regL (j.val / 2) = rRegL 0 (j.val / 2) := rfl
  have hV : regV (rowAt 0 k (j.val / 2)) (j.val % 2) = rRegV 0 (rowAt 0 k (j.val / 2)) (j.val % 2) :=
    rfl
  rw [e1, e2, x0, hL, hV]
  simp only [map_mul, map_inv, phiJ_eM, perm_reg]

theorem l37_fix
    {k : ℕ} (hk : k < 9) :
    ∃ w : Fin nPts, ∀ t ∈ CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven.LSub 0 k,
      phiJ t • w = w := by
  obtain ⟨hw, hfix⟩ := x0_fix hk
  refine ⟨⟨W.getD k 0, hw⟩, fun t ht => ?_⟩
  have hgen : ∀ j : Fin 4, phiJ (lY 0 k j) • (⟨W.getD k 0, hw⟩ : Fin nPts) = ⟨W.getD k 0, hw⟩ := by
    intro j
    have h := congrArg (fun σ : Equiv.Perm (Fin nPts) => σ ⟨W.getD k 0, hw⟩) (perm_lY (k := k) j)
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply] at h
    rw [h]
    apply Fin.ext
    rw [← idx_of_lt _ hw]
    exact hfix j.val j.isLt
  let S : Subgroup GM := (MulAction.stabilizer J (⟨W.getD k 0, hw⟩ : Fin nPts)).comap phiJ
  have hLS : CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven.LSub 0 k ≤ S := by
    unfold CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven.LSub
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgen i
  exact hLS ht

end Model

end CertificateChecks.KernelSpor.ONL37

end
