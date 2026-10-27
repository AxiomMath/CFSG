module

public import Certificates.Kernel.LyDce.CoverGlue
public import Certificates.Kernel.LyDce.Facts
public import Certificates.Kernel.LyDce.ConjChecks
public import CFSG.Certificates.Kernel.LyDce.ConjSound
public import CFSG.Certificates.Kernel.TwistDce.Cover
import all Certificates.Kernel.LyDce.CoverGlue
import all Certificates.Kernel.LyDce.BWord
import CFSG.Sporadic.Recognition.LyonsFinalFamiliesBase
import CFSG.Sporadic.Recognition.LyonsFinalFamilyInputs
import CFSG.Sporadic.Recognition.LyonsFinalGlue
import CFSG.Sporadic.Recognition.LyonsFinalMain
public import CFSG.Sporadic.Th.Max3.Core
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Recognition.CoverTransferWords
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut
public import CFSG.Sporadic.Recognition.LyonsSimsRecognition
public import CFSG.Sporadic.Schreier.J4SThree
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import Certificates.Certificate3085Base

public section

namespace CertificateChecks.KernelLyDce

open Equiv CFSG.KC.LyDce CFSG.KC.LyReplay CFSG.KC.LyBenes CFSG.KC.LyBase CFSG.KC.LyGlue
  CertificateChecks.KernelLyBase CertificateChecks.KernelLy CertificateChecks.KernelLyB
  CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.LyonsSims.LyFinal
  CFSG.CosetTable CFSG.Certificates.TwDce

noncomputable abbrev val (w : List (Fin 6 × Bool)) : PG 6 R18 :=
  FreeGroup.lift gen18 (FreeGroup.mk w)

noncomputable abbrev Hcd : Subgroup (PG 6 R18) :=
  genSub {r : FreeGroup (Fin 6) | r ∈ R18.map FreeGroup.mk} (subsetOf 6 [0, 1])

noncomputable def SGG (n : Nat) : Subgroup (PG 6 R18) :=
  Subgroup.closure {z | ∃ g ∈ sG.getD n [], z = val (wordOf g)}

noncomputable def Sn : Nat → Subgroup (PG 6 R18)
  | 0 => Hcd
  | n + 1 => SGG n

noncomputable def xR (i : Nat) : PG 6 R18 := val (wordOf (rootC i))

def HasFact (i : Nat) (z : PG 6 R18) : Prop :=
  ∃ p < 68, (nt.getD p (0, 0)).1 = i ∧ z = val (wordOf (rep.getD p []))

def repS (i : Nat) : Set (PG 6 R18) := {z | HasFact i z}

open Classical in
noncomputable def tgtElt (i : Nat) (z : PG 6 R18) : PG 6 R18 :=
  if h : HasFact i z then val (wordOf (vw.getD h.choose [])) else 1

theorem rb_mem18 : ∀ r ∈ RB, r ∈ R18 := fun r hr => core_mem (rb_mem_core r hr)

theorem rb_rel18 : ∀ r ∈ RB, FreeGroup.lift gen18 (FreeGroup.mk r) = 1 := fun r hr =>
  lift_rel_eq_one (rb_mem18 r hr)

noncomputable def psi : PG _ RB5 →* PG 6 R18 := PresentedGroup.toGroup (rb5_rel gen18 rb_rel18)

theorem psi_of (j : Fin S5.length) : psi (PresentedGroup.of j) = gen18 (S5.get j) :=
  PresentedGroup.toGroup.of (rb5_rel gen18 rb_rel18)

theorem psi_lift {w : List (Fin 6 × Bool)} {w' : List (Fin S5.length × Bool)}
    (h : renumber S5 w = some w') :
    psi (FreeGroup.lift (fun j => (PresentedGroup.of j : PG _ RB5)) (FreeGroup.mk w')) =
      val w := by
  rw [hom_lift]
  have e : (fun j => psi (PresentedGroup.of j : PG _ RB5)) = fun j => gen18 (S5.get j) := by
    funext j
    exact psi_of j
  rw [e, lift_renumber S5 gen18 h]

theorem letIdx_lt6 : ∀ l : Fin 6 × Bool, letIdx l < 6 → l.1.val < 5 := by decide +kernel

theorem isBWord_jw {g : List Nat} (h : ∀ j ∈ jwOf g, j < 6) : isBWord (wordOf g) = true :=
  (isBWord_iff _).2 fun l hl => letIdx_lt6 l (h _ (List.mem_map_of_mem hl))

theorem xR_zero : xR 0 = 1 := lift_mk_nil gen18

theorem xR_one : xR (0 + 1) = gen18 5 := lift_mk_kLetter gen18

theorem gen18_five_inv : (gen18 5)⁻¹ = gen18 5 :=
  inv_eq_of_mul_eq_one_right (gen18_inv 5 (by decide))

theorem p_lt {p m : Nat} (h : (nt.getD p (0, 0)).1 = m) (hm : m ≠ 0) : p < 68 := by
  by_contra hp
  have e : nt[p]? = none := List.getElem?_eq_none (by rw [nt_length]; omega)
  rw [List.getD_eq_getElem?_getD, e, Option.getD_none] at h
  exact hm h.symm

theorem rel_EorD : ∀ r ∈ modularE ++ modularD, FreeGroup.lift gen18 (FreeGroup.mk r) = 1 := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact lift_rel_eq_one (core_mem (E_mem r h))
  · exact lift_rel_eq_one (List.mem_append_right _ h)

theorem conj_mem' {n : Nat} (hn : n < 4) (hval : ∀ z, isBWord z = true → val z ∈ Hcd) :
    ∀ s ∈ SGG n, xR (n + 1) * s * (xR (n + 1))⁻¹ ∈ Hcd := by
  have hle : SGG n ≤ Hcd.comap (MulAut.conj (xR (n + 1))).toMonoidHom := by
    rw [SGG, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨z, hz, ez⟩ := conjOK_sound gen18_inv (conj_ok n hn) rel_EorD g hg
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    change val (wordOf (rootC (n + 1))) * val (wordOf g) * (val (wordOf (rootC (n + 1))))⁻¹ ∈ Hcd
    rw [ez]
    exact Hcd.inv_mem (hval z hz)
  intro s hs
  have h := hle hs
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

section Transfer

variable (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
  (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound)
include hc hd hbc

noncomputable def theta : Ly0.B0 →* PG 6 R18 :=
  psi.comp (MulEquiv.ofBijective (rb5ToB0 hc hd)
    ⟨rb5ToB0_injective hc hd hbc, rb5ToB0_surjective hc hd⟩).symm.toMonoidHom

theorem theta_rb5 (y : PG _ RB5) : theta hc hd hbc (rb5ToB0 hc hd y) = psi y := by
  change psi ((MulEquiv.ofBijective (rb5ToB0 hc hd)
    ⟨rb5ToB0_injective hc hd hbc, rb5ToB0_surjective hc hd⟩).symm (rb5ToB0 hc hd y)) = psi y
  congr 1
  exact (MulEquiv.ofBijective (rb5ToB0 hc hd)
    ⟨rb5ToB0_injective hc hd hbc, rb5ToB0_surjective hc hd⟩).symm_apply_apply y

theorem theta_lift {w : List (Fin 6 × Bool)} (hb : isBWord w = true) :
    theta hc hd hbc (FreeGroup.lift gBs (FreeGroup.mk w)) = val w := by
  obtain ⟨w', hw'⟩ := renumber_some S5 w fun l hl => mem_S5 l.1 ((isBWord_iff w).1 hb l hl)
  have hy : rb5ToB0 hc hd (FreeGroup.lift (fun j => (PresentedGroup.of j : PG _ RB5))
      (FreeGroup.mk w')) = FreeGroup.lift gBs (FreeGroup.mk w) := by
    rw [hom_lift]
    have e : (fun j => rb5ToB0 hc hd (PresentedGroup.of j)) = fun j => gBs (S5.get j) := by
      funext j
      rw [rb5ToB0, PresentedGroup.toGroup.of]
    rw [e, lift_renumber S5 gBs hw']
  rw [← hy, theta_rb5, psi_lift hw']

theorem theta_wP {g : List Nat} (hb : isBWord (wordOf g) = true) :
    theta hc hd hbc ⟨wP (jwOf g), wP_mem _⟩ = val (wordOf g) := by
  have e : (⟨wP (jwOf g), wP_mem _⟩ : Ly0.B0) = FreeGroup.lift gBs (FreeGroup.mk (wordOf g)) :=
    Subtype.ext (by rw [coe_lift_gBs, lift_gB_eq_wG hc hd hb]; rfl)
  rw [e, theta_lift hc hd hbc hb]

theorem theta_mem (x : Ly0.B0) : theta hc hd hbc x ∈ Hcd := by
  have e0 : S5.get ⟨0, by decide⟩ = 0 := by decide
  have e1 : S5.get ⟨1, by decide⟩ = 1 := by decide
  have g0 : gB 0 = Ly0.cG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_zero]
  have g1 : gB 1 = Ly0.dG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_one]
  have m0 : (0 : Fin 6) ∈ subsetOf 6 [0, 1] := by decide
  have m1 : (1 : Fin 6) ∈ subsetOf 6 [0, 1] := by decide
  have h : (⊤ : Subgroup Ly0.B0) ≤ Hcd.comap (theta hc hd hbc) := by
    rw [← Subgroup.closure_closure_coe_preimage, Subgroup.closure_le]
    rintro ⟨x, hx⟩ hx'
    rcases hx' with h | h
    · have e : rb5ToB0 hc hd (PresentedGroup.of ⟨0, by decide⟩) = ⟨x, hx⟩ := by
        rw [rb5ToB0, PresentedGroup.toGroup.of, e0]
        exact Subtype.ext (g0.trans h.symm)
      change theta hc hd hbc ⟨x, hx⟩ ∈ Hcd
      rw [← e, theta_rb5, psi_of, e0]
      exact Subgroup.subset_closure ⟨0, m0, rfl⟩
    · have e : rb5ToB0 hc hd (PresentedGroup.of ⟨1, by decide⟩) = ⟨x, hx⟩ := by
        rw [rb5ToB0, PresentedGroup.toGroup.of, e1]
        exact Subtype.ext (g1.trans (Set.mem_singleton_iff.1 h).symm)
      change theta hc hd hbc ⟨x, hx⟩ ∈ Hcd
      rw [← e, theta_rb5, psi_of, e1]
      exact Subgroup.subset_closure ⟨1, m1, rfl⟩
  exact h (Subgroup.mem_top x)

theorem theta_surj {h : PG 6 R18} (hh : h ∈ Hcd) : ∃ x, theta hc hd hbc x = h := by
  have hle : Hcd ≤ (theta hc hd hbc).range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hiS : i ∈ S5 := by
      revert i
      decide
    obtain ⟨j, hj⟩ := List.get_of_mem hiS
    exact ⟨rb5ToB0 hc hd (PresentedGroup.of j), by rw [theta_rb5, psi_of, hj]⟩
  exact hle hh

theorem val_mem {w : List (Fin 6 × Bool)} (hb : isBWord w = true) : val w ∈ Hcd := by
  rw [← theta_lift hc hd hbc hb]
  exact theta_mem hc hd hbc _

theorem theta_SG (n : Nat) {s : Perm (Fin Ly0.deg)} (hs : s ∈ SG n) :
    theta hc hd hbc ⟨s, SG_le n hs⟩ ∈ SGG n := by
  have hle : SG n ≤ ((SGG n).comap (theta hc hd hbc)).map Ly0.B0.subtype := by
    rw [SG, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨wP (jwOf g), wP_mem _⟩, ?_, rfl⟩
    change theta hc hd hbc ⟨wP (jwOf g), wP_mem _⟩ ∈ SGG n
    rw [theta_wP hc hd hbc (isBWord_jw (sG_lt' n g hg))]
    exact Subgroup.subset_closure ⟨g, hg, rfl⟩
  obtain ⟨b, hb, e⟩ := hle hs
  have eb : b = ⟨s, SG_le n hs⟩ := Subtype.ext e
  rw [← eb]
  exact hb

theorem SGG_le (n : Nat) : SGG n ≤ Hcd := by
  rw [SGG, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact val_mem hc hd hbc (isBWord_jw (sG_lt' n g hg))

theorem conj_mem {n : Nat} (hn : n < 4) : ∀ s ∈ SGG n, xR (n + 1) * s * (xR (n + 1))⁻¹ ∈ Hcd :=
  conj_mem' hn fun _ hz => val_mem hc hd hbc hz

theorem repS_le (i : Nat) : ∀ z ∈ repS i, z ∈ Hcd := by
  rintro _ ⟨p, hp, -, rfl⟩
  exact val_mem hc hd hbc (fact_holds hc hd hbc hp).2.2.1

theorem cover0 : ∀ h ∈ Hcd, ∃ k ∈ repS 0, ∃ s ∈ Hcd, ∃ c ∈ SGG 0, h = s * k * c := by
  intro h hh
  have h0 : (nt.getD 0 (0, 0)).1 = 0 := by decide +kernel
  have hk := val_mem hc hd hbc (fact_holds hc hd hbc (i := 0) (by decide)).2.2.1
  refine ⟨_, ⟨0, by decide, h0, rfl⟩, h * (val (wordOf (rep.getD 0 [])))⁻¹,
    Hcd.mul_mem hh (Hcd.inv_mem hk), 1, (SGG 0).one_mem, by group⟩

theorem coverN {n : Nat} (hn : n < 4) :
    ∀ h ∈ Hcd, ∃ k ∈ repS (n + 1), ∃ s ∈ SGG n, ∃ c ∈ SGG 0, h = s * k * c := by
  intro h hh
  obtain ⟨g, rfl⟩ := theta_surj hc hd hbc hh
  obtain ⟨s, hs, r, ⟨p, hp, rfl⟩, y, hy, e⟩ := cover_node hc hd hbc hn g.1 g.2
  have hp68 := p_lt hp (Nat.succ_ne_zero n)
  have hb := (fact_holds hc hd hbc hp68).2.2.1
  refine ⟨_, ⟨p, hp68, hp, rfl⟩, _, theta_SG hc hd hbc n hs, _, theta_SG hc hd hbc 0 hy, ?_⟩
  have eg : g = ⟨s, SG_le n hs⟩ * ⟨wP (jwOf (rep.getD p [])), wP_mem _⟩ * ⟨y, SG_le 0 hy⟩ :=
    Subtype.ext e
  rw [eg, map_mul, map_mul, theta_wP hc hd hbc hb]

open Classical in
noncomputable def tgt (i : Nat) (z : PG 6 R18) : Fin 5 :=
  if h : HasFact i z then
    ⟨(nt.getD h.choose (0, 0)).2, (fact_holds hc hd hbc h.choose_spec.1).2.1⟩
  else 0

theorem tgtElt_mem (i : Nat) (z : PG 6 R18) : tgtElt i z ∈ Hcd := by
  unfold tgtElt
  split_ifs with h
  · exact val_mem hc hd hbc (fact_holds hc hd hbc h.choose_spec.1).2.2.2.1
  · exact Hcd.one_mem

theorem tgt_spec (i : Nat) {z : PG 6 R18} (hz : HasFact i z) :
    xR i * z * gen18 5 * (xR (tgt hc hd hbc i z).val * tgtElt i z)⁻¹ ∈ Hcd := by
  have ht : (tgt hc hd hbc i z).val = (nt.getD hz.choose (0, 0)).2 := by
    unfold tgt
    rw [dif_pos hz]
  have hv : tgtElt i z = val (wordOf (vw.getD hz.choose [])) := by
    unfold tgtElt
    rw [dif_pos hz]
  rw [ht, hv]
  obtain ⟨hp, hi, hzp⟩ := hz.choose_spec
  obtain ⟨-, -, -, -, ha, e⟩ := fact_holds hc hd hbc hp
  generalize hz.choose = p at hp hi hzp ha e ⊢
  subst hzp hi
  have e' : xR (nt.getD p (0, 0)).1 * val (wordOf (rep.getD p [])) * gen18 5 =
      val (wordOf (aw.getD p [])) * xR (nt.getD p (0, 0)).2 * val (wordOf (vw.getD p [])) := e
  rw [e', mul_assoc (val _) (xR _), mul_inv_cancel_right]
  exact val_mem hc hd hbc ha

noncomputable def twist : TwistData Hcd (SGG 0) (gen18 5) 5 where
  x i := xR i
  S i := Sn i
  rep i := repS i
  tgt i z := tgt hc hd hbc i z
  tgtElt i z := tgtElt i z
  base := 0
  base_mem := by
    change xR 0 ∈ Hcd
    rw [xR_zero]
    exact Hcd.one_mem
  S_le := by
    rintro ⟨_ | n, hi⟩
    · exact le_rfl
    · exact SGG_le hc hd hbc n
  S_conj := by
    rintro ⟨_ | n, hi⟩ s hs
    · change xR 0 * s * (xR 0)⁻¹ ∈ Hcd
      rw [xR_zero, one_mul, inv_one, mul_one]
      exact hs
    · exact conj_mem hc hd hbc (by omega) s hs
  rep_le i := repS_le hc hd hbc i
  rep_cover := by
    rintro ⟨_ | n, hi⟩
    · exact cover0 hc hd hbc
    · exact coverN hc hd hbc (by omega)
  tgtElt_mem i z _ := tgtElt_mem hc hd hbc i z
  tgt_spec i z hz := tgt_spec hc hd hbc i hz

theorem relIndex_le {n : Nat} (hn : n < 4) :
    (SGG n).relIndex Hcd * ordS.getD n 0 ≤ 5388768000 := by
  let θ' : Ly0.B0 →* Hcd := (theta hc hd hbc).codRestrict Hcd (theta_mem hc hd hbc)
  have hθ' : Function.Surjective θ' := by
    rintro ⟨h, hh⟩
    obtain ⟨x, hx⟩ := theta_surj hc hd hbc hh
    exact ⟨x, Subtype.ext hx⟩
  let K := (SG n).subgroupOf Ly0.B0
  have hle : K.map θ' ≤ (SGG n).subgroupOf Hcd := by
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (theta_SG hc hd hbc n (Subgroup.mem_subgroupOf.1 hb))
  have h1 : (SGG n).relIndex Hcd ≤ K.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero K.index_ne_zero_of_finite)
      ((Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd (H := K) hθ'))
  have e1 : Nat.card K = Nat.card (SG n) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (SG_le n)).toEquiv
  have e2 := K.index_mul_card
  rw [e1] at e2
  calc (SGG n).relIndex Hcd * ordS.getD n 0 ≤ K.index * Nat.card (SG n) :=
        Nat.mul_le_mul h1 (card_SG_ge hc hd hn)
    _ = Nat.card Ly0.B0 := e2
    _ ≤ 5388768000 := card_B0_le hc hd hbc

theorem hgen : Subgroup.closure ((Hcd : Set (PG 6 R18)) ∪ {gen18 5}) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i.val < 5
  · apply Subgroup.subset_closure
    left
    have e : (PresentedGroup.of i : PG 6 R18) = val [(i, true)] := by
      simp [val, lift_mk_cons, lift_mk_nil]
    rw [e]
    exact val_mem hc hd hbc ((isBWord_iff _).2 (by simpa using hi))
  · apply Subgroup.subset_closure
    right
    have e : i = 5 := Fin.ext (by omega)
    rw [e]
    rfl

theorem index_cd : Hcd.FiniteIndex ∧ Hcd.index ≤ 9606125 := by
  have : Finite Hcd := (card_cd_le rb_mem18 hbc).1
  have huC : ∀ c ∈ SGG 0, (gen18 5)⁻¹ * c * gen18 5 ∈ Hcd := by
    intro c hc'
    have h := conj_mem hc hd hbc (n := 0) (by decide) c hc'
    rw [xR_one, gen18_five_inv] at h
    rw [gen18_five_inv]
    exact h
  obtain ⟨hfi, hidx⟩ := (twist hc hd hbc).index_le_sum (gen18_inv 5 (by decide)) huC
    (hgen hc hd hbc)
  refine ⟨hfi, hidx.trans ?_⟩
  rw [Fin.sum_univ_five]
  change Hcd.relIndex Hcd + (SGG 0).relIndex Hcd + (SGG 1).relIndex Hcd + (SGG 2).relIndex Hcd +
    (SGG 3).relIndex Hcd ≤ 9606125
  rw [Subgroup.relIndex_self]
  have b0 := relIndex_le hc hd hbc (n := 0) (by decide)
  have b1 := relIndex_le hc hd hbc (n := 1) (by decide)
  have b2 := relIndex_le hc hd hbc (n := 2) (by decide)
  have b3 := relIndex_le hc hd hbc (n := 3) (by decide)
  have o0 : ordS.getD 0 0 = 349920 := rfl
  have o1 : ordS.getD 1 0 = 10080 := rfl
  have o2 : ordS.getD 2 0 = 2880 := rfl
  have o3 : ordS.getD 3 0 = 750 := rfl
  rw [o0] at b0
  rw [o1] at b1
  rw [o2] at b2
  rw [o3] at b3
  have t0 : (SGG 0).relIndex Hcd ≤ 15400 :=
    Nat.le_of_mul_le_mul_right (b0.trans (by norm_num)) (by norm_num)
  have t1 : (SGG 1).relIndex Hcd ≤ 534600 :=
    Nat.le_of_mul_le_mul_right (b1.trans (by norm_num)) (by norm_num)
  have t2 : (SGG 2).relIndex Hcd ≤ 1871100 :=
    Nat.le_of_mul_le_mul_right (b2.trans (by norm_num)) (by norm_num)
  have t3 : (SGG 3).relIndex Hcd ≤ 7185024 :=
    Nat.le_of_mul_le_mul_right (b3.trans (by norm_num)) (by norm_num)
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl t0) t1) t2)
    t3).trans (by norm_num)

end Transfer

end CertificateChecks.KernelLyDce

end
