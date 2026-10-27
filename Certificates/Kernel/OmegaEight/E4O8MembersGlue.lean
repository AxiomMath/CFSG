module

public import Certificates.Kernel.OmegaEight.E4O8NbrGlue
public import Certificates.Kernel.OmegaEight.E4O8MembersC0
public import Certificates.Kernel.OmegaEight.E4O8MembersC1
public import Certificates.Kernel.OmegaEight.E4O8MembersC2
public import Certificates.Kernel.OmegaEight.E4O8MembersC3
public import Certificates.Kernel.OmegaEight.E4O8MembersC4
public import Certificates.Kernel.OmegaEight.E4O8MembersC5
public import Certificates.Kernel.OmegaEight.E4O8MembersC6
public import Certificates.Kernel.OmegaEight.E4O8MembersC7
public import Certificates.Kernel.OmegaEight.E4O8MembersC8
public import Certificates.Kernel.OmegaEight.E4O8MembersC9
public import Certificates.Kernel.OmegaEight.E4O8MembersC10
public import Certificates.Kernel.OmegaEight.E4O8MembersC11
public import Certificates.Kernel.OmegaEight.E4O8MembersC12
public import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Data.E189E4tO8
public import CFSG.Certificates.Kernel.EvenSporSuz.Sound
import Std.Data.String.ToNat
import all Init.Data.List.SplitOn.Basic
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridgeBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4
open CFSG.KLC.E8 (strictB_eq')

theorem e4_bAnd (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem e4_bIf_not (a : Bool) : bIf(a, false, true) = !a := by cases a <;> rfl

theorem e4_of_bIf {c a : Bool} (h : bIf(c, a, true) = true) (hc : c = true) : a = true := by
  subst hc
  exact h

theorem e4_semi : (";" : String) = String.singleton ';' := by rw [String.singleton_eq_ofList]

theorem e4_toNat_nil : (String.ofList ([] : List Char)).toNat? = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  intro n hn
  exact (String.isNat_iff.1 (String.isNat_of_toNat?_eq_some hn)).1 rfl

theorem e4_parseNats {p : List Char} (h : e4Piece p = true) :
    E4O8.parseNats (String.ofList p) = e4Nats p := by
  cases p with
  | nil =>
    unfold E4O8.parseNats
    rw [CFSG.KC.EvenSporSuz.space_eq, CFSG.KC.Str.splitOn_ofList]
    have hs : ([] : List Char).splitOn ' ' = [[]] := rfl
    rw [hs, List.map_cons, List.map_nil, List.filterMap_cons, e4_toNat_nil]
    rfl
  | cons c p =>
    have hd : ((c :: p).splitOn ' ').all CFSG.KC.EvenSporSuz.digitsK = true := by
      simpa [e4Piece] using h
    have e : E4O8.parseNats (String.ofList (c :: p)) =
        CFSG.EvenSporadicStandard.TwoSuz.parseNats (String.ofList (c :: p)) := rfl
    rw [e, CFSG.KC.EvenSporSuz.parseNats_ofList _ hd]
    rfl

theorem e4_pieces : (e4MS.chars.splitOn ';').map e4Nats = e4MR.map Prod.fst ∧
    ∀ p ∈ e4MS.chars.splitOn ';', e4Piece p = true := by
  have h := kE4Parse
  rw [e4_bAnd, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨of_decide_eq_true h2, List.all_eq_true.1 h1⟩

theorem wsW_eq : E4O8.wsW () = e4MR.map fun r => E4O8.toWord r.1 := by
  obtain ⟨hp, hn⟩ := e4_pieces
  unfold E4O8.wsW E4O8.parseRows
  rw [e4MS.eq, e4_semi, CFSG.KC.Str.splitOn_ofList]
  have hx : ((e4MS.chars.splitOn ';').map String.ofList).map E4O8.parseNats =
      e4MR.map Prod.fst := by
    rw [List.map_map, ← hp]
    exact List.map_congr_left fun p hp' => e4_parseNats (hn p hp')
  rw [hx, List.map_map]
  rfl

theorem e4_all_of_chunks {α : Type} {R : List α} {f : α → Bool} {n : Nat} (hR : R.length ≤ 16 * n)
    (h : ∀ s < n, ((R.drop (Nat.mul 16 s)).take 16).all f = true) : ∀ r ∈ R, f r = true := by
  intro r hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  have hs := List.all_eq_true.1 (h (k / 16) (by omega))
  apply hs
  have hk' : k % 16 < ((R.drop (Nat.mul 16 (k / 16))).take 16).length := by
    simp only [List.length_take, List.length_drop, Nat.mul_eq]
    omega
  have hm := List.getElem_mem hk'
  rw [List.getElem_take, List.getElem_drop] at hm
  have e : Nat.mul 16 (k / 16) + k % 16 = k := by
    rw [Nat.mul_eq]
    omega
  simp only [e] at hm
  exact hm

theorem e4_len : e4MR.length = 6300 := Nat.eq_of_beq_eq_true kE4Len

theorem e4L_eq : e4L = [pid, mainK 0, e4U, pc e4U (mainK 0), om0V, pc om0V (mainK 0),
    pc e4U om0V, pc (pc e4U om0V) (mainK 0)] := rfl

theorem e4_chunk {s : Nat} (h : e4Chunk s = true) : e4RowsAt (mainK 0) e4U om0V e4L s = true := by
  unfold e4Chunk at h
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq',
    strictB_eq'] at h
  rw [e4L_eq]
  exact h

#kc_forall_tree ch294002mAll (fun s => e4Chunk s = true) 394
  CertificateChecks.KernelO8.ch294002m

theorem e4_chunks : ∀ s < 394, e4RowsAt (mainK 0) e4U om0V e4L s = true :=
  fun s hs => e4_chunk (ch294002mAll s hs)

theorem e4_rows : ∀ r ∈ e4MR, e4Row (mainK 0) e4U om0V e4L r = true :=
  e4_all_of_chunks (n := 394) (by rw [e4_len]; decide) fun s hs => e4_chunks s hs

theorem e4_row_at {k : Nat} (hk : k < 6300) :
    e4RowK (mainK 0) e4U om0V e4L (e4WW k) (e4MR.getD k ([], (0, 0))).2.1
      (e4MR.getD k ([], (0, 0))).2.2 = true := by
  have h' : k < e4MR.length := by rw [e4_len]; exact hk
  exact e4_rows (e4MR.getD k ([], (0, 0)))
    (by rw [List.getD_eq_getElem _ _ h']; exact List.getElem_mem h')

theorem e4_row_facts {wd : List Int} {l j : Nat} (h : e4RowK (mainK 0) e4U om0V e4L wd l j = true) :
    lettersK 17 wd = true ∧ cn (wO wd) = true ∧ e4Pm (wO wd) = true ∧
      e4Pm (cj (wO wd) (mainK 0)) = true ∧
      e4TAt (mainK 0) e4U om0V e4L (cj (wO wd) (mainK 0)) l = true ∧
      e4SAt (mainK 0) e4U om0V e4L (wO wd) (cj (wO wd) (mainK 0)) j = true := by
  unfold e4RowK at h
  rw [strictB_eq', strictB_eq'] at h
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

@[expose] noncomputable def e4WP : List Nat := e4MR.map fun r => wO (E4O8.toWord r.1)

theorem e4WP_length : e4WP.length = 6300 := by
  unfold e4WP
  rw [List.length_map, e4_len]

theorem e4WP_getD {k : Nat} (hk : k < 6300) : e4WP.getD k 0 = wO (e4WW k) := by
  unfold e4WP e4WW
  exact getD_map_of_lt _ _ _ (by rw [e4_len]; exact hk)

theorem wsA_pk : E4O8.wsA () = e4WP.map (unpack 360 9) := by
  unfold E4O8.wsA e4WP
  rw [wsW_eq, List.map_map, List.map_map]
  refine List.map_congr_left fun r hr => ?_
  exact omegaW_eq (e4_row_facts (e4_rows r hr)).1

theorem e4_ws_getD {k : Nat} (hk : k < 6300) :
    (e4WP.map (unpack 360 9)).getD k (idA 360) = unpack 360 9 (wO (e4WW k)) := by
  rw [getD_map_of_lt (unpack 360 9) 0 (idA 360) (by rw [e4WP_length]; exact hk), e4WP_getD hk]

theorem commGensA_pk {i j b : Nat} (hi : cn i = true) (hj : cn j = true) (hb : cn b = true) :
    E4A.commGensA 360 (unpack 360 9 i) (unpack 360 9 j) (unpack 360 9 b) = e4Comm i j b := by
  unfold E4A.commGensA e4Comm
  rw [compA_pc hb hi, compA_pc hi hb, compA_pc hb hj, compA_pc hj hb,
    eqA_pc (cn_pc hb hi) (cn_pc hi hb), eqA_pc (cn_pc hb hj) (cn_pc hj hb), e4_bAnd]

theorem goodWitA_pk {t x : Nat} (ht : cn t = true) (hx : cn x = true)
    (h : e4GoodK e4U om0V (pc (mainK 0) t) x (pc x t) = true) :
    E4A.goodWitA 360 (unpack 360 9 (mainK 0)) (unpack 360 9 e4U) (unpack 360 9 om0V)
      (unpack 360 9 t) (unpack 360 9 x) = true := by
  obtain ⟨-, cu, -, cv, cx0, -⟩ := e4_facts
  unfold e4GoodK at h
  simp only [bAnd_iff] at h
  obtain ⟨hpx, hpxt, h1, h2⟩ := h
  obtain ⟨px, cxi⟩ := e4Pm_iff.1 hpx
  obtain ⟨pxt, cxti⟩ := e4Pm_iff.1 hpxt
  have crt := cn_pc cx0 ht
  have cxt := cn_pc hx ht
  unfold E4A.goodWitA
  rw [compA_pc cx0 ht, invCand_pinv px, compA_pc cxi crt, compA_pc (cn_pc cxi crt) hx,
    compA_pc hx ht, invCand_pinv pxt, compA_pc cxti crt, compA_pc (cn_pc cxti crt) cxt,
    commGensA_pk cu cv (cn_pc (cn_pc cxi crt) hx), commGensA_pk cu cv (cn_pc (cn_pc cxti crt) cxt),
    h1, h2]
  rfl

theorem e4TRel_eq (t : Nat) : e4TRel (mainK 0) e4U om0V e4L t =
    (Nat.beq (pc t (mainK 0)) (pc (mainK 0) t) && !e4Norms e4L e4U om0V t) := by
  unfold e4TRel
  rw [e4_bIf_not, e4_bAnd]

theorem e4SRel_eq (w t : Nat) : e4SRel (mainK 0) e4U om0V e4L w t =
    (Nat.beq t (mainK 0) && !e4Norms e4L e4U om0V w) := by
  unfold e4SRel
  rw [e4_bIf_not, e4_bAnd]

theorem tcheck_k : E4O8.tcheck () = true := by
  obtain ⟨-, cu, -, cv, cx0, ex⟩ := e4_facts
  unfold E4O8.tcheck
  rw [L0A_pk, u0A_pk, v0A_pk, ex, wsA_pk]
  unfold E4A.tCheckA
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range, List.length_map, e4WP_length] at hk
  rw [e4_ws_getD hk]
  obtain ⟨-, cw, pw, pt, hT, -⟩ := e4_row_facts (e4_row_at hk)
  obtain ⟨pmw, cwi⟩ := e4Pm_iff.1 pw
  obtain ⟨pmt, cti⟩ := e4Pm_iff.1 pt
  have ct := cn_cj cw cwi cx0
  rw [conjA_pk cw cwi pmw cx0]
  unfold E4A.memberOKA E4A.relevantTA
  rw [compA_pc ct cx0, compA_pc cx0 ct, eqA_pc (cn_pc ct cx0) (cn_pc cx0 ct),
    normsA_pk e4L_cn cu cv ct cti pmt, ← e4TRel_eq]
  unfold e4TAt at hT
  cases hr : e4TRel (mainK 0) e4U om0V e4L (cj (wO (e4WW k)) (mainK 0))
  · rfl
  · have ha := e4_of_bIf hT hr
    simp only [bAnd_iff] at ha
    obtain ⟨hl, hlet, hg⟩ := ha
    have hl' := of_blt hl
    rw [strictB_eq'] at hg
    unfold e4Good at hg
    rw [strictB_eq', strictB_eq'] at hg
    obtain ⟨cx, hgk⟩ := (bAnd_iff _ _).1 hg
    rw [Bool.not_true, Bool.false_or]
    refine List.any_eq_true.2 ⟨(e4MR.getD k ([], (0, 0))).2.1,
      List.mem_range.2 (by rw [List.length_map, e4WP_length]; exact hl'), ?_⟩
    rw [e4_ws_getD hl']
    exact goodWitA_pk ct cx hgk

theorem e4_split_len : (E4O8.splitW ()).length = 2 := rfl

theorem e4Cand_facts {c : Nat} (hc : c < 2) :
    lettersK 17 ((E4O8.splitW ()).getD c []) = true ∧ cn (e4Cand c) = true ∧
      e4Pm (e4Cand c) = true ∧ Nat.beq (pc (e4Cand c) (e4Cand c)) (pinv (e4Cand c)) = true ∧
      e4Norms e4L e4U om0V (e4Cand c) = true ∧ e4Comm e4U om0V (e4Cand c) = false := by
  have h := allN_spec kE4Cand c hc
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq',
    strictB_eq', ← e4L_eq] at h
  unfold e4CandK at h
  simp only [bAnd_iff] at h
  obtain ⟨h2, h3, h4, h5, h6⟩ := h
  rw [e4_bIf_not, Bool.not_eq_true'] at h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem splitWitA_pk {w c : Nat} (cw : cn w = true) (cwi : cn (pinv w) = true) (pmw : pm w = true)
    (hc : c < 2) (h : e4Comm (cj w e4U) (cj w om0V) (e4Cand c) = true) :
    E4A.splitWitA 360 (e4L.map (unpack 360 9)) (unpack 360 9 e4U) (unpack 360 9 om0V)
      (unpack 360 9 w) (unpack 360 9 (e4Cand c)) = true := by
  obtain ⟨-, cu, -, cv, -, -⟩ := e4_facts
  obtain ⟨-, cc, pc', h4, h5, h6⟩ := e4Cand_facts hc
  obtain ⟨pmc, cci⟩ := e4Pm_iff.1 pc'
  unfold E4A.splitWitA
  rw [compA_pc cc cc, invCand_pinv pmc, eqA_pc (cn_pc cc cc) cci, normsA_pk e4L_cn cu cv cc cci pmc,
    conjA_pk cw cwi pmw cu, conjA_pk cw cwi pmw cv,
    commGensA_pk (cn_cj cw cwi cu) (cn_cj cw cwi cv) cc, commGensA_pk cu cv cc, h4, h5, h, h6]
  rfl

theorem e4_wordsOK_split : E4O8.wordsOK (E4O8.splitW ()) = true := by decide +kernel

theorem scheck_k : E4O8.scheck () = true := by
  obtain ⟨-, cu, -, cv, cx0, ex⟩ := e4_facts
  unfold E4O8.scheck
  rw [Bool.and_eq_true]
  refine ⟨e4_wordsOK_split, ?_⟩
  rw [L0A_pk, u0A_pk, v0A_pk, ex, wsA_pk]
  unfold E4O8.splitA
  unfold E4A.splitCheckA
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range, List.length_map, e4WP_length] at hk
  rw [e4_ws_getD hk]
  obtain ⟨-, cw, pw, -, -, hS⟩ := e4_row_facts (e4_row_at hk)
  obtain ⟨pmw, cwi⟩ := e4Pm_iff.1 pw
  have ct := cn_cj cw cwi cx0
  unfold E4A.splitOKA
  rw [conjA_pk cw cwi pmw cx0, eqA_pc ct cx0, normsA_pk e4L_cn cu cv cw cwi pmw, ← e4SRel_eq]
  unfold e4SAt at hS
  cases hr : e4SRel (mainK 0) e4U om0V e4L (wO (e4WW k)) (cj (wO (e4WW k)) (mainK 0))
  · rfl
  · have ha := e4_of_bIf hS hr
    obtain ⟨hj, hcomm⟩ := (bAnd_iff _ _).1 ha
    have hj' := of_blt hj
    rw [Bool.not_true, Bool.false_or]
    have hjl : (e4MR.getD k ([], (0, 0))).2.2 < (E4O8.splitW ()).length := by
      rw [e4_split_len]; exact hj'
    have hjm := List.getElem_mem hjl
    rw [← List.getD_eq_getElem _ [] hjl] at hjm
    refine List.any_eq_true.2 ⟨_, List.mem_map_of_mem hjm, ?_⟩
    rw [omegaW_eq (e4Cand_facts hj').1]
    exact splitWitA_pk cw cwi pmw hj' hcomm

end CertificateChecks.KernelO8

end
