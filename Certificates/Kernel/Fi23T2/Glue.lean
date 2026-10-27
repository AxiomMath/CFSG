module

public import Certificates.Kernel.Fi23T2.ChkDefs
public import Certificates.Kernel.Fi23S.Tables
public import Certificates.Kernel.Fi23M.Keys
public import CFSG.Sporadic.Fi23.Classes
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.LargeInv
import Certificates.Kernel.Fi23T2.Sl0
import Certificates.Kernel.Fi23T2.Sl1
import Certificates.Kernel.Fi23T2.Sl2
import Certificates.Kernel.Fi23T2.Sl3
import Certificates.Kernel.Fi23T2.Misc
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Fi22
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.Walter.JRFacts
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620Base
public import Certificates.Certificate13622Base
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

#kon_join CFSG.KD.Fi23T2.slAll CFSG.KD.Fi23T2.slF 16

namespace CertificateChecks.KernelFi23T2

open CFSG.KC.Enum CFSG.KD.Fi23T2 CFSG.KS.Raw.Orb CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi23 (J slvl TS tabS sylG rep_tabS rep_LS_all exists_tree_mul slvl_two
  syl_facts TS_size LS_size)
open CFSG.EvenSporadicStandard.YS14 (IsLargeInv)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Count

variable {G : Type*} [Group G] [Finite G]

theorem card_cent_mul_le (x : G) (g : Fin 9 → G)
    (hg : Function.Injective fun t => g t * x * (g t)⁻¹) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) * 9 ≤ Nat.card G := by
  set C := Subgroup.centralizer ({x} : Set G)
  have hinj : Function.Injective fun t => (QuotientGroup.mk (g t) : G ⧸ C) := by
    intro s t hst
    apply hg
    have h := QuotientGroup.eq.1 hst
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    change g s * x * (g s)⁻¹ = g t * x * (g t)⁻¹
    calc g s * x * (g s)⁻¹ = g s * (x * ((g s)⁻¹ * g t)) * (g t)⁻¹ := by group
      _ = g s * ((g s)⁻¹ * g t * x) * (g t)⁻¹ := by rw [← h]
      _ = g t * x * (g t)⁻¹ := by group
  have h9 : 9 ≤ C.index := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin] at this
  calc Nat.card C * 9 ≤ Nat.card C * C.index := Nat.mul_le_mul_left _ h9
    _ = Nat.card G := C.card_mul_index

theorem card_le_cent (x : G) (L : List G) (hL : L.length ≤ 8)
    (hc : ∀ g : G, g * x * g⁻¹ ∈ L) :
    Nat.card G ≤ Nat.card (Subgroup.centralizer ({x} : Set G)) * 8 := by
  classical
  set C := Subgroup.centralizer ({x} : Set G)
  set S := L.toFinset
  have hS : S.card ≤ 8 := (List.toFinset_card_le L).trans hL
  have hc' : ∀ g : G, g * x * g⁻¹ ∈ S := fun g => List.mem_toFinset.2 (hc g)
  let f : G ⧸ C → S := Quotient.lift (fun g => ⟨g * x * g⁻¹, hc' g⟩) (by
    intro a b hab
    have h : a⁻¹ * b ∈ C := QuotientGroup.leftRel_apply.1 hab
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    apply Subtype.ext
    change a * x * a⁻¹ = b * x * b⁻¹
    calc a * x * a⁻¹ = a * (x * (a⁻¹ * b)) * b⁻¹ := by group
      _ = a * (a⁻¹ * b * x) * b⁻¹ := by rw [← h]
      _ = b * x * b⁻¹ := by group)
  have hf : Function.Injective f := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with | H a => ?_
    induction q using QuotientGroup.induction_on with | H b => ?_
    have h : a * x * a⁻¹ = b * x * b⁻¹ := congrArg Subtype.val hpq
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a⁻¹ * b * x = a⁻¹ * (b * x * b⁻¹) * b := by group
      _ = a⁻¹ * (a * x * a⁻¹) * b := by rw [h]
      _ = x * (a⁻¹ * b) := by group
  have hi : C.index ≤ 8 := by
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := S), Fintype.card_coe] at this
    exact this.trans hS
  calc Nat.card G = Nat.card C * C.index := C.card_mul_index.symm
    _ ≤ Nat.card C * 8 := Nat.mul_le_mul_left _ hi

end Count

theorem lenK_eq {α : Type} : ∀ l : List α, lenK l = l.length
  | [] => rfl
  | _ :: l => by rw [List.length_cons, ← lenK_eq l]; rfl

theorem neAll_spec {f : Nat → Nat} {k : Nat} : ∀ {l : List Nat}, neAll f k l = true →
    ∀ b ∈ l, k ≠ f b
  | [], _, b, hb => absurd hb List.not_mem_nil
  | c :: l, h, b, hb => by
    change bAnd(Bool.not (Nat.beq k (f c)), neAll f k l) = true at h
    rw [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · intro e
      rw [e, Nat.beq_refl] at h
      exact Bool.noConfusion h.1
    · exact neAll_spec h.2 b hb

theorem distK_spec {f : Nat → Nat} : ∀ {l : List Nat}, distK f l = true →
    l.Pairwise fun a b => f a ≠ f b
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    change bAnd(strictB (f a) fun k => neAll f k l, distK f l) = true at h
    rw [bAnd_eq, Bool.and_eq_true, strictB_eq] at h
    exact List.Pairwise.cons (neAll_spec h.1) (distK_spec h.2)

theorem codesOK_spec : ∀ {l : List Nat}, codesOK l = true → ∀ u ∈ l, u < 1806
  | [], _, u, hu => absurd hu List.not_mem_nil
  | c :: l, h, u, hu => by
    change bAnd(Nat.blt c (nat_lit 1806), codesOK l) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact Nat.blt_eq.mp h.1
    · exact codesOK_spec h.2 u hu

theorem wOK_spec {e : List Nat} (h : wOK e = true) :
    e = [hd e, 0] ∨ ∃ us : List Nat, e = hd e :: 1 :: us ∧ us.length = 9 ∧
      (∀ u ∈ us, u < 1806) ∧ us.Pairwise fun a b => kyL (hd e) a ≠ kyL (hd e) b := by
  match e, h with
  | i :: tag :: us, h =>
    change bIf(Nat.beq tag (nat_lit 0), Nat.beq (lenK us) (nat_lit 0),
        bAnd(Nat.beq tag (nat_lit 1), bAnd(Nat.beq (lenK us) (nat_lit 9),
          bAnd(codesOK us, distK (kyL i) us)))) = true at h
    change i :: tag :: us = [i, 0] ∨ ∃ us' : List Nat, i :: tag :: us = i :: 1 :: us' ∧
      us'.length = 9 ∧ (∀ u ∈ us', u < 1806) ∧ us'.Pairwise fun a b => kyL i a ≠ kyL i b
    rw [bIf_eq] at h
    split_ifs at h with h0
    · left
      have ht : tag = 0 := Nat.eq_of_beq_eq_true h0
      have hu : us = [] := List.eq_nil_of_length_eq_zero (by
        rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true h)
      rw [ht, hu]
    · right
      rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨us, by rw [Nat.eq_of_beq_eq_true h1], ?_, codesOK_spec h3, distK_spec h4⟩
      rw [← lenK_eq]
      exact Nat.eq_of_beq_eq_true h2
  | [], h => exact Bool.noConfusion h
  | [_], h => exact Bool.noConfusion h

theorem memH_spec {i : Nat} : ∀ {L : List (List Nat)}, memH i L = true → ∃ e ∈ L, hd e = i
  | [], h => Bool.noConfusion h
  | e :: L, h => by
    change bIf(Nat.beq (hd e) i, true, memH i L) = true at h
    rw [bIf_eq] at h
    split_ifs at h with h0
    · exact ⟨e, List.mem_cons_self, Nat.eq_of_beq_eq_true h0⟩
    · obtain ⟨e', he', h'⟩ := memH_spec h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

theorem entsK_spec : ∀ {L : List (List Nat)}, entsK L = true → ∀ e ∈ L, wOK e = true
  | [], _, e, he => absurd he List.not_mem_nil
  | c :: L, h, e, he => by
    change bAnd(wOK c, entsK L) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact entsK_spec h.2 e he

theorem mem_largeOf {i : Nat} : ∀ {L : List (List Nat)}, [i, 0] ∈ L → i ∈ largeOf L
  | [], h => absurd h List.not_mem_nil
  | e :: L, h => by
    change i ∈ Bool.rec (motive := fun _ => List Nat) (largeOf L) (hd e :: largeOf L)
      (Nat.beq (List.getD e (nat_lit 1) (nat_lit 1)) (nat_lit 0))
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · cases Nat.beq (List.getD e (nat_lit 1) (nat_lit 1)) (nat_lit 0)
      · exact mem_largeOf h
      · exact List.mem_cons_of_mem _ (mem_largeOf h)

theorem mem_largeS {i : Nat} : ∀ {S : List (List (List Nat))} {s : Nat},
    [i, 0] ∈ List.getD S s [] → i ∈ List.rec (motive := fun _ => List Nat) []
      (fun sl _ ih => largeOf sl ++ ih) S
  | [], s, h => by rw [List.getD_nil] at h; exact absurd h List.not_mem_nil
  | c :: S, s, h => by
    change i ∈ largeOf c ++ List.rec (motive := fun _ => List Nat) []
      (fun sl _ ih => largeOf sl ++ ih) S
    cases s with
    | zero => exact List.mem_append_left _ (mem_largeOf h)
    | succ s =>
      rw [List.getD_cons_succ] at h
      exact List.mem_append_right _ (mem_largeS h)

theorem covered {i : Nat} (hi : i < 262144)
    (hc : 2 ≤ CFSG.KD.Fi23S.code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511))) :
    ∃ e, hd e = i ∧ wOK e = true ∧ (e = [i, 0] → i ∈ large) := by
  have hs : i / 16384 < 16 := by omega
  have h := slAll _ hs
  unfold slF at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hcov, hents⟩ := h
  unfold covK at hcov
  have hlt : i - i / 16384 * 16384 < 16384 := by omega
  have hd' := allN_iff.1 hcov (i - i / 16384 * 16384) hlt
  have e1 : Nat.add (Nat.mul (i / 16384) (nat_lit 16384)) (i - i / 16384 * 16384) = i := by
    have : i / 16384 * 16384 + (i - i / 16384 * 16384) = i := by omega
    exact this
  have hn : ¬ Nat.blt (CFSG.KD.Fi23S.code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511)))
      (nat_lit 2) = true := fun h => by
    have h' : CFSG.KD.Fi23S.code (Nat.shiftRight i (nat_lit 9)) (Nat.land i (nat_lit 511)) < 2 :=
      Nat.blt_eq.mp h
    omega
  rw [strictB_eq, e1, strictB_eq, bIf_eq, if_neg hn] at hd'
  obtain ⟨e, he, hhd⟩ := memH_spec hd'
  refine ⟨e, hhd, entsK_spec hents e he, fun h0 => ?_⟩
  rw [h0] at he
  exact mem_largeS he

theorem commK_spec {a b : Nat} (h : commK a b = true) :
    ∀ x < 6, gL a (gL b x) = gL b (gL a x) := fun x hx =>
  Nat.eq_of_beq_eq_true (allN_iff.1 h x hx)

theorem allComm_spec {a : Nat} : ∀ {t : List Nat},
    List.rec (motive := fun _ => Bool) true (fun b _ ih2 => bAnd(commK a b, ih2)) t = true →
    ∀ b ∈ t, commK a b = true
  | [], _, b, hb => absurd hb List.not_mem_nil
  | c :: t, h, b, hb => by
    change bAnd(commK a c, List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => bAnd(commK a b, ih2)) t) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact allComm_spec h.2 b hb

theorem rc_pairwise : ∀ {l : List Nat}, List.rec (motive := fun _ => Bool) true
    (fun a t ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => bAnd(commK a b, ih2)) t, ih)) l = true →
    l.Pairwise fun a b => commK a b = true
  | [], _ => List.Pairwise.nil
  | a :: t, h => by
    change bAnd(List.rec (motive := fun _ => Bool) true
      (fun b _ ih2 => bAnd(commK a b, ih2)) t, List.rec (motive := fun _ => Bool) true
      (fun a t ih => bAnd(List.rec (motive := fun _ => Bool) true
        (fun b _ ih2 => bAnd(commK a b, ih2)) t, ih)) t) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    exact List.Pairwise.cons (allComm_spec h.1) (rc_pairwise h.2)

theorem shr9 (i : Nat) : Nat.shiftRight i (nat_lit 9) = i / 512 := Nat.shiftRight_eq_div_pow i 9

theorem land511 (i : Nat) : Nat.land i (nat_lit 511) = i % 512 :=
  Nat.and_two_pow_sub_one_eq_mod i 9

theorem shr1 (i : Nat) : Nat.shiftRight i (nat_lit 1) = i / 2 := Nat.shiftRight_eq_div_pow i 1

theorem land1 (i : Nat) : Nat.land i (nat_lit 1) = i % 2 := Nat.and_two_pow_sub_one_eq_mod i 1

theorem pw_mem {R : Nat → Nat → Prop} : ∀ {l : List Nat}, l.Pairwise R → ∀ {a b : Nat},
    a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha'
    · rcases List.mem_cons.1 hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hne
      · rw [ha']
        exact Or.inl (h.1 b hb')
    · rcases List.mem_cons.1 hb with hb' | hb'
      · rw [hb']
        exact Or.inr (h.1 a ha')
      · exact pw_mem h.2 ha' hb' hne

theorem subP_cons (a : Nat) (l : List Nat) (s x : Nat) :
    subP (a :: l) s x = if s % 2 = 1 then gL a (subP l (s / 2) x) else subP l (s / 2) x := by
  change strictN (subP l (Nat.shiftRight s (nat_lit 1)) x) (fun y =>
    nIf(Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1), gL a y, y)) = _
  rw [strictN_eq, nIf_eq, shr1, land1]
  by_cases h : s % 2 = 1
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · rw [if_neg h, if_neg (fun e => h (Nat.eq_of_beq_eq_true e))]

section J


theorem LS_eq : CFSG.Sporadic.Fi23.LS = CertificateChecks.KernelFi23S.SL := by
  change sylLetters (chainLetters (orbitData ())) = sylLetters (chainLetters CFSG.KD.Fi23K.orbLit)
  rw [CFSG.KD.Fi23K.orbitData_eq']

theorem tabS_eq (i : Nat) : tabS i = treeTabs 31671
    (chainTrees 31671 CertificateChecks.KernelFi23S.SL sylBase)[i]!
      CertificateChecks.KernelFi23S.SL := by
  change treeTabs 31671 (chainTrees 31671 CFSG.Sporadic.Fi23.LS sylBase)[i]!
    CFSG.Sporadic.Fi23.LS = _
  rw [LS_eq]

theorem TS_pts {t : Nat} (ht : t < 2) : TS[t]!.pts.size = 512 := by
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · exact TS_size (l := 0) rfl
  · exact TS_size (l := 1) rfl

theorem idx_tree {t k y : Nat} (ht : t < 2) (hk : k < 512) (hy : y < 31671) :
    idx 31671 (CFSG.Perm.treeG TS[t]! (CFSG.Perm.pairG sylG) k) y = CFSG.KD.Fi23S.wS t k y := by
  have hs : k < TS[t]!.pts.size := by rw [TS_pts ht]; exact hk
  rw [← rep_tabS (by change t < 2; exact ht) hs y hy, tabS_eq,
    CertificateChecks.KernelFi23S.treeTabs_ap ht hk hy,
    CertificateChecks.KernelFi23S.wS_eq ht hk hy]

@[expose] noncomputable def eL (i : Nat) : CFSG.Sporadic.Fi23.J :=
  CFSG.Perm.treeG TS[0]! (CFSG.Perm.pairG sylG) (i / 512) *
    CFSG.Perm.treeG TS[1]! (CFSG.Perm.pairG sylG) (i % 512)

theorem gL_eq (i x : Nat) : gL i x = CFSG.KD.Fi23S.gK (i / 512) (i % 512) x := by
  unfold gL
  rw [shr9, land511]

theorem idx_e {i y : Nat} (hi : i < 262144) (hy : y < 31671) : idx 31671 (eL i) y = gL i y := by
  unfold eL
  rw [idx_mul, idx_tree (by decide) (by omega) hy,
    idx_tree (by decide) (by omega) (by
      rw [← idx_tree (by decide) (by omega) hy]; exact idx_lt _ hy), gL_eq]
  rfl

theorem eL_mem (i : Nat) (hi : i < 262144) : eL i ∈ slvl 0 := by
  have h0 := (syl_facts.1 0 (by decide)).treeG_mem (k := i / 512) (by rw [TS_pts (by decide)]; omega)
  have h1 := (syl_facts.1 1 (by decide)).treeG_mem (k := i % 512) (by rw [TS_pts (by decide)]; omega)
  exact (slvl 0).mul_mem h0 (CFSG.Perm.levelGroup_anti _ (by decide : 0 ≤ 1) h1)

theorem exists_e {x : CFSG.Sporadic.Fi23.J} (hx : x ∈ slvl 0) : ∃ i < 262144, x = eL i := by
  obtain ⟨k, hk, h, hh, rfl⟩ := exists_tree_mul (i := 0) (by decide) hx
  obtain ⟨j, hj, h', hh', rfl⟩ := exists_tree_mul (i := 1) (by decide) hh
  rw [slvl_two, Subgroup.mem_bot] at hh'
  rw [hh', mul_one]
  rw [TS_pts (by decide)] at hk hj
  refine ⟨512 * k + j, by omega, ?_⟩
  unfold eL
  rw [show (512 * k + j) / 512 = k by omega, show (512 * k + j) % 512 = j by omega]

theorem idx_lG {l x : Nat} (hl : l < 42) (hx : x < 31671) :
    idx 31671 (CFSG.Perm.pairG sylG l) x = CFSG.KD.Fi23S.LS l x := by
  have hl' : l < CFSG.Sporadic.Fi23.LS.size := by
    rw [LS_size]; change l < 2 * 21; omega
  rw [← rep_LS_all l hl' x hx, LS_eq]
  exact CFSG.KS.PC.ap_letter CertificateChecks.KernelFi23S.syl_hyp hl hx

theorem lG_mem {l : Nat} (hl : l < 42) : CFSG.Perm.pairG sylG l ∈ slvl 0 := by
  refine CFSG.Perm.lG_mem (CFSG.Perm.mem_levelLetters_zero.2 ?_)
  rw [LS_size]; change l < 2 * 21; omega

theorem invL_lt42 {l : Nat} (hl : l < 42) : Nat.xor l 1 < 42 := by
  rw [CFSG.KS.PC.xor_one]
  exact CFSG.Perm.invL_lt (by decide) hl

theorem lG_inv (l : Nat) : (CFSG.Perm.pairG sylG l)⁻¹ = CFSG.Perm.pairG sylG (Nat.xor l 1) := by
  rw [CFSG.KS.PC.xor_one, CFSG.Perm.pairG_invL]

@[expose] noncomputable def cE (u : Nat) : CFSG.Sporadic.Fi23.J :=
  if u < 42 then CFSG.Perm.pairG sylG u
  else CFSG.Perm.pairG sylG ((u - 42) / 42) * CFSG.Perm.pairG sylG ((u - 42) % 42)

theorem cE_mem {u : Nat} (hu : u < 1806) : cE u ∈ slvl 0 := by
  unfold cE
  split_ifs with h
  · exact lG_mem h
  · exact (slvl 0).mul_mem (lG_mem (by omega)) (lG_mem (by omega))

theorem gL_lt {i y : Nat} (hi : i < 262144) (hy : y < 31671) : gL i y < 31671 := by
  rw [← idx_e hi hy]
  exact idx_lt _ hy

theorem LS_lt' {l x : Nat} (hl : l < 42) (hx : x < 31671) : CFSG.KD.Fi23S.LS l x < 31671 :=
  CertificateChecks.KernelFi23S.LS_lt hl hx

theorem idx_conj {u i p : Nat} (hu : u < 1806) (hi : i < 262144) (hp : p < 31671) :
    idx 31671 (cE u * eL i * (cE u)⁻¹) p = cjL u i p := by
  unfold cE cjL
  rw [nIf_eq]
  by_cases h : u < 42
  · rw [if_pos h, if_pos (Nat.blt_eq.mpr h), lG_inv, idx_mul, idx_mul,
      idx_lG (invL_lt42 h) hp, idx_e hi (LS_lt' (invL_lt42 h) hp),
      idx_lG h (gL_lt hi (LS_lt' (invL_lt42 h) hp))]
  · rw [if_neg h, if_neg (fun e => h (Nat.blt_eq.mp e)), strictN_eq, strictN_eq, strictN_eq]
    have ha : (u - 42) / 42 < 42 := by omega
    have hb : (u - 42) % 42 < 42 := Nat.mod_lt _ (by decide)
    change idx 31671 (CFSG.Perm.pairG sylG ((u - 42) / 42) * CFSG.Perm.pairG sylG ((u - 42) % 42) *
      eL i * (CFSG.Perm.pairG sylG ((u - 42) / 42) * CFSG.Perm.pairG sylG ((u - 42) % 42))⁻¹) p =
      CFSG.KD.Fi23S.LS ((u - 42) / 42) (CFSG.KD.Fi23S.LS ((u - 42) % 42)
        (gL i (CFSG.KD.Fi23S.LS (Nat.xor ((u - 42) % 42) 1)
          (CFSG.KD.Fi23S.LS (Nat.xor ((u - 42) / 42) 1) p))))
    have h1 := LS_lt' (invL_lt42 ha) hp
    have h2 := LS_lt' (invL_lt42 hb) h1
    have h3 := gL_lt hi h2
    rw [mul_inv_rev, lG_inv, lG_inv]
    simp only [idx_mul]
    rw [idx_lG (invL_lt42 ha) hp, idx_lG (invL_lt42 hb) h1, idx_e hi h2, idx_lG hb h3,
      idx_lG ha (LS_lt' hb h3)]

attribute [local irreducible] eL cE

theorem eq_six {x y : CFSG.Sporadic.Fi23.J} (h : ∀ t < 6, idx 31671 x t = idx 31671 y t) : x = y :=
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow.eq_of_base h

theorem card_T : Nat.card (slvl 0) = 262144 := CFSG.Sporadic.Fi23.card_slvl_zero

theorem finite_T : Finite (slvl 0) := Nat.finite_of_card_ne_zero (by rw [card_T]; norm_num)

theorem lt_of_six {t : Nat} (ht : t < 6) : t < 31671 := by omega

theorem large_leaf (x : ↥(slvl 0)) (hx : IsLargeInv x) :
    ∃ i < 262144, i ∈ large ∧ (x : CFSG.Sporadic.Fi23.J) = eL i := by
  have : Finite (slvl 0) := finite_T
  obtain ⟨i, hi, hxi⟩ := exists_e x.2
  have hk : Nat.shiftRight i (nat_lit 9) < 512 := by rw [shr9]; omega
  have hj : Nat.land i (nat_lit 511) < 512 := by rw [land511]; omega
  have hsq : ∀ b < 6, gL i (gL i b) = b := by
    intro b hb
    have h1 : (x : J) * x = 1 := by rw [← Subgroup.coe_mul, hx.1, Subgroup.coe_one]
    have h2 := congrArg (fun g => idx 31671 g b) h1
    simp only [idx_mul, idx_one] at h2
    rw [hxi, idx_e hi (lt_of_six hb), idx_e hi (gL_lt hi (lt_of_six hb))] at h2
    exact h2
  rcases CertificateChecks.KernelFi23S.lf13_cases (CertificateChecks.KernelFi23S.lf13_all hk hj)
    with ⟨_, b, hb, hne⟩ | ⟨_, hfix⟩ | ⟨hc, _⟩ | ⟨hc, _⟩
  · exact absurd (hsq b hb) hne
  · exfalso
    apply hx.2.1
    apply Subtype.ext
    rw [hxi, Subgroup.coe_one]
    apply eq_six
    intro t ht
    rw [idx_e hi (lt_of_six ht), idx_one]
    exact hfix t ht
  all_goals
    obtain ⟨e, hhd, hw, hlarge⟩ := covered hi hc
    rcases wOK_spec hw with h0 | ⟨us, -, hlen, hlt, hpw⟩
    · exact ⟨i, hi, hlarge (by rw [h0, hhd]), hxi⟩
    · exfalso
      rw [hhd] at hpw
      have hu : ∀ t : Fin 9, us[t.val]'(by rw [hlen]; exact t.isLt) < 1806 :=
        fun t => hlt _ (List.getElem_mem _)
      let g : Fin 9 → ↥(slvl 0) := fun t => ⟨cE (us[t.val]'(by rw [hlen]; exact t.isLt)),
        cE_mem (hu t)⟩
      have hnd : (us.map (kyL i)).Nodup := List.pairwise_map.2 hpw
      have hinj : Function.Injective fun t => g t * x * (g t)⁻¹ := by
        intro s t hst
        have h2 := congrArg (fun y : ↥(slvl 0) => (y : J)) hst
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, g] at h2
        rw [hxi] at h2
        have k0 := congrArg (fun y => idx 31671 y 0) h2
        have k2 := congrArg (fun y => idx 31671 y 2) h2
        rw [idx_conj (hu s) hi (by decide), idx_conj (hu t) hi (by decide)] at k0 k2
        have hky : kyL i (us[s.val]'(by rw [hlen]; exact s.isLt)) =
            kyL i (us[t.val]'(by rw [hlen]; exact t.isLt)) := by
          unfold kyL
          rw [k0, k2]
        have e2 := (List.Nodup.getElem_inj_iff hnd (i := s.val) (j := t.val)
          (hi := by rw [List.length_map, hlen]; exact s.isLt)
          (hj := by rw [List.length_map, hlen]; exact t.isLt)).1
          (by rw [List.getElem_map, List.getElem_map]; exact hky)
        exact Fin.ext e2
      have hc9 := card_cent_mul_le x g hinj
      rw [card_T] at hc9
      have hl := hx.2.2
      omega

theorem large_comm (x y : ↥(slvl 0)) (hx : IsLargeInv x) (hy : IsLargeInv y) : x * y = y * x := by
  obtain ⟨a, ha, hal, hxa⟩ := large_leaf x hx
  obtain ⟨b, hb, hbl, hyb⟩ := large_leaf y hy
  have hpw := rc_pairwise (l := large) rcOK
  have hab : ∀ t < 6, gL a (gL b t) = gL b (gL a t) := by
    by_cases e : a = b
    · intro t _; rw [e]
    · rcases pw_mem hpw hal hbl e with h | h
      · exact commK_spec h
      · exact fun t ht => (commK_spec h t ht).symm
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hxa, hyb]
  apply eq_six
  intro t ht
  rw [idx_mul, idx_mul, idx_e hb (lt_of_six ht), idx_e ha (lt_of_six ht),
    idx_e ha (gL_lt hb (lt_of_six ht)), idx_e hb (gL_lt ha (lt_of_six ht))]
  exact hab t ht

theorem conjIn_spec {t y : Nat} : ∀ {l : List Nat}, conjIn t y l = true →
    ∃ z ∈ l, ∀ x < 6, CFSG.KD.Fi23S.LS t (gL y x) = gL z (CFSG.KD.Fi23S.LS t x)
  | [], h => Bool.noConfusion h
  | z :: l, h => by
    change bIf(allN (nat_lit 6) fun x => Nat.beq (CFSG.KD.Fi23S.LS t (gL y x))
      (gL z (CFSG.KD.Fi23S.LS t x)), true, conjIn t y l) = true at h
    rw [bIf_eq] at h
    split_ifs at h with h0
    · exact ⟨z, List.mem_cons_self, fun x hx => Nat.eq_of_beq_eq_true (allN_iff.1 h0 x hx)⟩
    · obtain ⟨z', hz', h'⟩ := conjIn_spec h
      exact ⟨z', List.mem_cons_of_mem _ hz', h'⟩

theorem clRec_spec {l : List Nat} : ∀ {m : List Nat}, List.rec (motive := fun _ => Bool) true
    (fun y _ ih => bAnd(Nat.blt y (nat_lit 262144),
      bAnd(allN (nat_lit 42) fun t => conjIn t y l, ih))) m = true →
    ∀ y ∈ m, y < 262144 ∧ ∀ t < 42, conjIn t y l = true
  | [], _, y, hy => absurd hy List.not_mem_nil
  | c :: m, h, y, hy => by
    change bAnd(Nat.blt c (nat_lit 262144), bAnd(allN (nat_lit 42) fun t => conjIn t c l,
      List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(Nat.blt y (nat_lit 262144),
        bAnd(allN (nat_lit 42) fun t => conjIn t y l, ih))) m)) = true at h
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨Nat.blt_eq.mp h.1, fun t ht => allN_iff.1 h.2.1 t ht⟩
    · exact clRec_spec h.2.2 y hy

theorem clK_spec {l : List Nat} (h : clK l = true) : 0 < l.length ∧ l.length ≤ 8 ∧
    ∀ y ∈ l, y < 262144 ∧ ∀ t < 42, conjIn t y l = true := by
  unfold clK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, lenK_eq] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.ble_eq.mp h.2.1, clRec_spec h.2.2⟩

theorem class_closed {l : List Nat} (hcl : clK l = true) {g : CFSG.Sporadic.Fi23.J} (hg : g ∈ slvl 0) :
    ∀ y ∈ l, ∃ z ∈ l, g * eL y * g⁻¹ = eL z := by
  obtain ⟨-, -, hall⟩ := clK_spec hcl
  have hlet : ∀ t < 42, ∀ y ∈ l, ∃ z ∈ l,
      CFSG.Perm.pairG sylG t * eL y * (CFSG.Perm.pairG sylG t)⁻¹ = eL z := by
    intro t ht y hy
    obtain ⟨hyb, hconj⟩ := hall y hy
    obtain ⟨z, hz, hzx⟩ := conjIn_spec (hconj t ht)
    have hzb := (hall z hz).1
    have e : CFSG.Perm.pairG sylG t * eL y = eL z * CFSG.Perm.pairG sylG t := eq_six fun x hx => by
      rw [idx_mul, idx_mul, idx_e hyb (lt_of_six hx), idx_lG ht (gL_lt hyb (lt_of_six hx)),
        idx_lG ht (lt_of_six hx), idx_e hzb (LS_lt' ht (lt_of_six hx))]
      exact hzx x hx
    exact ⟨z, hz, by rw [e, mul_inv_cancel_right]⟩
  change g ∈ Subgroup.closure {g | ∃ l' ∈ CFSG.Perm.Native.levelLetters
    CFSG.Sporadic.Fi23.LS sylBase 0, CFSG.Perm.pairG sylG l' = g} at hg
  have h42 : ∀ {t : Nat}, t ∈ CFSG.Perm.Native.levelLetters CFSG.Sporadic.Fi23.LS sylBase 0 →
      t < 42 := fun ht => by
    have := CFSG.Perm.mem_levelLetters_zero.1 ht
    rw [LS_size] at this
    exact this
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact hlet t (h42 ht)
  | inv_mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    rw [lG_inv]
    exact hlet _ (invL_lt42 (h42 ht))
  | one => exact fun y hy => ⟨y, hy, by group⟩
  | mul x y _ _ hx hy =>
    intro w hw
    obtain ⟨z1, hz1, e1⟩ := hy w hw
    obtain ⟨z2, hz2, e2⟩ := hx z1 hz1
    exact ⟨z2, hz2, by rw [← e2, ← e1]; group⟩

theorem cK_spec {r : Nat} (hr : r < 7) :
    hd (List.getD D.C r []) = List.getD D.B r 0 ∧ List.getD D.B r 0 < 262144 ∧
      (∀ x < 6, gL (List.getD D.B r 0) (gL (List.getD D.B r 0) x) = x) ∧
      (¬ ∀ x < 6, gL (List.getD D.B r 0) x = x) ∧ clK (List.getD D.C r []) = true := by
  have h := cOK
  unfold cK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  have h1 := allN_iff.1 h.2 r hr
  rw [strictB_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at h1
  obtain ⟨e1, e2, e3, e4, e5⟩ := h1
  refine ⟨Nat.eq_of_beq_eq_true e1, Nat.blt_eq.mp e2,
    fun x hx => Nat.eq_of_beq_eq_true (allN_iff.1 e3 x hx), fun hc => ?_, e5⟩
  rw [Bool.not_eq_true', ← Bool.not_eq_true] at e4
  exact e4 (allN_iff.2 fun x hx => by rw [hc x hx]; exact Nat.beq_refl x)

theorem large_of {b : Nat} {l : List Nat} (hb : b < 262144) (hhd : hd l = b)
    (hsq : ∀ x < 6, gL b (gL b x) = x) (hmov : ¬ ∀ x < 6, gL b x = x) (hcl : clK l = true) :
    IsLargeInv (⟨eL b, eL_mem _ hb⟩ : ↥(slvl 0)) := by
  have : Finite (slvl 0) := finite_T
  refine ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    apply eq_six
    intro t ht
    rw [idx_mul, idx_e hb (lt_of_six ht), idx_e hb (gL_lt hb (lt_of_six ht)), idx_one]
    exact hsq t ht
  · intro h1
    apply hmov
    intro t ht
    have h2 := congrArg (fun y : ↥(slvl 0) => idx 31671 (y : J) t) h1
    simp only [Subgroup.coe_one, idx_one] at h2
    rw [idx_e hb (lt_of_six ht)] at h2
    exact h2
  · obtain ⟨hpos, hlen, hall⟩ := clK_spec hcl
    have hbl : b ∈ l := by
      cases hl : l with
      | nil => rw [hl] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
      | cons z m =>
        have : hd l = z := by rw [hl]; rfl
        rw [← hhd, this]
        exact List.mem_cons_self
    let f : Nat → ↥(slvl 0) := fun z => if h : z < 262144 then ⟨eL z, eL_mem z h⟩ else 1
    have hS : (l.map f).length ≤ 8 := by rw [List.length_map]; exact hlen
    have hc : ∀ g : ↥(slvl 0), g * ⟨eL b, eL_mem _ hb⟩ * g⁻¹ ∈ l.map f := by
      intro g
      obtain ⟨z, hz, e⟩ := class_closed hcl g.2 b hbl
      rw [List.mem_map]
      refine ⟨z, hz, ?_⟩
      apply Subtype.ext
      have hzb := (hall z hz).1
      change ((if h : z < 262144 then (⟨eL z, eL_mem z h⟩ : ↥(slvl 0)) else 1 : ↥(slvl 0)) : J) =
        (g : J) * eL b * (g : J)⁻¹
      rw [dif_pos hzb, e]
    have h8 := card_le_cent (⟨eL b, eL_mem _ hb⟩ : ↥(slvl 0)) (l.map f) hS hc
    rw [card_T] at h8
    have h15 : (2 : ℕ) ^ 15 = 32768 := by norm_num
    rw [h15]
    omega

theorem basis_large {r : Nat} (hr : r < 7) (h : List.getD D.B r 0 < 262144) :
    IsLargeInv (⟨eL (List.getD D.B r 0), eL_mem _ h⟩ : ↥(slvl 0)) := by
  obtain ⟨hhd, hb, hsq, hmov, hcl⟩ := cK_spec hr
  exact large_of hb hhd hsq hmov hcl

@[expose] noncomputable def pB : List Nat → Nat → CFSG.Sporadic.Fi23.J
  | [], _ => 1
  | a :: l, s => (if s % 2 = 1 then eL a else 1) * pB l (s / 2)

theorem pB_nil (s : Nat) : pB [] s = 1 := rfl

theorem pB_cons (a : Nat) (l : List Nat) (s : Nat) :
    pB (a :: l) s = (if s % 2 = 1 then eL a else 1) * pB l (s / 2) := rfl

attribute [local irreducible] pB

theorem idx_pB : ∀ {l : List Nat}, (∀ a ∈ l, a < 262144) → ∀ s x, x < 31671 →
    idx 31671 (pB l s) x = subP l s x
  | [], _, s, x, _ => by rw [pB_nil, idx_one]; rfl
  | a :: l, hl, s, x, hx => by
    have ha := hl a List.mem_cons_self
    have ih := idx_pB (fun b hb => hl b (List.mem_cons_of_mem _ hb)) (s / 2) x hx
    rw [pB_cons, idx_mul, ih, subP_cons]
    have hlt : subP l (s / 2) x < 31671 := by rw [← ih]; exact idx_lt _ hx
    split_ifs
    · rw [idx_e ha hlt]
    · rw [idx_one]

theorem pB_mem : ∀ {l : List Nat}, (∀ a ∈ l, a < 262144) → ∀ s, pB l s ∈ slvl 0
  | [], _, s => by
    rw [pB_nil]
    exact (slvl 0).one_mem
  | a :: l, hl, s => by
    rw [pB_cons]
    refine (slvl 0).mul_mem ?_ (pB_mem (fun b hb => hl b (List.mem_cons_of_mem _ hb)) _)
    split_ifs
    · exact eL_mem a (hl a List.mem_cons_self)
    · exact (slvl 0).one_mem

theorem pB_closure : ∀ {l : List Nat} (hl : ∀ a ∈ l, a < 262144),
    (∀ a ∈ l, ∀ h : a < 262144, IsLargeInv (⟨eL a, eL_mem a h⟩ : ↥(slvl 0))) →
    ∀ s (h : pB l s ∈ slvl 0), (⟨pB l s, h⟩ : ↥(slvl 0)) ∈
      Subgroup.closure {x : ↥(slvl 0) | IsLargeInv x}
  | [], _, _, s, h => by
    have e : (⟨pB [] s, h⟩ : ↥(slvl 0)) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_one]; exact pB_nil s)
    rw [e]
    exact (Subgroup.closure _).one_mem
  | a :: l, hl, hlarge, s, h => by
    have ha := hl a List.mem_cons_self
    have hl' : ∀ b ∈ l, b < 262144 := fun b hb => hl b (List.mem_cons_of_mem _ hb)
    have ih := pB_closure hl' (fun b hb h => hlarge b (List.mem_cons_of_mem _ hb) h) (s / 2)
      (pB_mem hl' _)
    by_cases hs : s % 2 = 1
    · have e : (⟨pB (a :: l) s, h⟩ : ↥(slvl 0)) =
          (⟨eL a, eL_mem a ha⟩ : ↥(slvl 0)) * ⟨pB l (s / 2), pB_mem hl' _⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        change pB (a :: l) s = eL a * pB l (s / 2)
        rw [pB_cons, if_pos hs]
      rw [e]
      exact (Subgroup.closure _).mul_mem
        (Subgroup.subset_closure (hlarge a List.mem_cons_self ha)) ih
    · have e : (⟨pB (a :: l) s, h⟩ : ↥(slvl 0)) = ⟨pB l (s / 2), pB_mem hl' _⟩ := by
        apply Subtype.ext
        change pB (a :: l) s = pB l (s / 2)
        rw [pB_cons, if_neg hs, one_mul]
      rw [e]
      exact ih

theorem B_len : D.B.length = 7 := by
  have h := bOK
  unfold bK at h
  rw [bAnd_eq, Bool.and_eq_true, lenK_eq] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem B_spec {a : Nat} (ha : a ∈ D.B) : ∃ r < 7, List.getD D.B r 0 = a := by
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 ha
  exact ⟨r, by rw [← B_len]; exact hr, List.getD_eq_getElem _ _ hr⟩

theorem B_lt : ∀ a ∈ D.B, a < 262144 := fun a ha => by
  obtain ⟨r, hr, rfl⟩ := B_spec ha
  exact (cK_spec hr).2.1

theorem subKey_inj {s t : Nat} (hs : s < 128) (ht : t < 128) (h : subKey s = subKey t) : s = t := by
  have hb := bOK
  unfold bK at hb
  rw [bAnd_eq, Bool.and_eq_true] at hb
  have hnd : ((List.range 128).map subKey).Nodup := List.pairwise_map.2 (distK_spec hb.2)
  exact (List.Nodup.getElem_inj_iff hnd (i := s) (j := t)
    (hi := by rw [List.length_map, List.length_range]; exact hs)
    (hj := by rw [List.length_map, List.length_range]; exact ht)).1
    (by rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_range]; exact h)

theorem pB_inj {s t : Fin 128} (h : pB D.B s.val = pB D.B t.val) : s = t := by
  have k0 := congrArg (fun y => idx 31671 y 0) h
  have k2 := congrArg (fun y => idx 31671 y 2) h
  rw [idx_pB B_lt _ _ (by decide), idx_pB B_lt _ _ (by decide)] at k0 k2
  exact Fin.ext (subKey_inj s.isLt t.isLt (by unfold subKey; rw [k0, k2]))

theorem pB_inj' {s t : Fin 128} (h : (⟨pB D.B s.val, pB_mem B_lt s.val⟩ : ↥(slvl 0)) =
    ⟨pB D.B t.val, pB_mem B_lt t.val⟩) : s = t := pB_inj (Subtype.mk.inj h)

@[expose] noncomputable def vE : Fin 128 ↪ ↥(slvl 0) :=
  ⟨fun s => ⟨pB D.B s.val, pB_mem B_lt s.val⟩, fun _ _ h => pB_inj' h⟩

@[expose] noncomputable def V : Finset ↥(slvl 0) := Finset.univ.map vE

theorem card_V : V.card = 128 := by
  unfold V
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem V_mem : ∀ v ∈ V, v ∈ Subgroup.closure {x : ↥(slvl 0) | IsLargeInv x} := by
  intro v hv
  unfold V at hv
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.1 hv
  refine pB_closure B_lt (fun a ha h => ?_) s.val (pB_mem B_lt s.val)
  obtain ⟨r, hr, rfl⟩ := B_spec ha
  exact basis_large hr h

theorem factorization_two_pow_mul' (k m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem card_T_sylow : Nat.card (slvl 0) = 2 ^ (Nat.card CFSG.Sporadic.Fi23.J).factorization 2 := by
  rw [card_T, CFSG.Sporadic.Fi23.card_J,
    show (4089470473293004800 : ℕ) = 2 ^ 18 * 15600091832325 by norm_num,
    factorization_two_pow_mul' 18 15600091832325 (by norm_num)]
  norm_num

theorem t2_facts : ∃ T : Sylow 2 CFSG.Sporadic.Fi23.J,
    (∀ x y : ↥(T : Subgroup CFSG.Sporadic.Fi23.J), IsLargeInv x → IsLargeInv y → x * y = y * x) ∧
    ∃ V : Finset ↥(T : Subgroup CFSG.Sporadic.Fi23.J), 128 ≤ V.card ∧
      ∀ v ∈ V, v ∈ Subgroup.closure {x : ↥(T : Subgroup CFSG.Sporadic.Fi23.J) | IsLargeInv x} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi23.card_J]; norm_num)
  exact ⟨Sylow.ofCard (slvl 0) card_T_sylow, large_comm, V, card_V.ge, V_mem⟩

end J

end CertificateChecks.KernelFi23T2

end
