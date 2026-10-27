module

public import Certificates.Kernel.HN1023016.ChecksJCl
public import Certificates.Kernel.HN1023016.ChecksW
public import Certificates.Kernel.HNF26720.Facts
public import CFSG.Certificates.Kernel.SlpPcSound
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClassesCl
public import CFSG.Sporadic.HNSchreier.Order
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
public import CFSG.Certificates.Kernel.Fam.Lin

public section

namespace CertificateChecks.KernelHN1023016

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.F5 CFSG.StandardType.SporadicShape
open CFSG.Sporadic.HNSchreier.Native
open CFSG.KS.SlpPc CFSG.KD.HN1023016 CertificateChecks.KernelHNF26720

theorem consts9 : CFSG.KC.Ord.constsOK 5 13 117 9 9 L9 H9 CM9 RM9 ONE9 LV9 HV9 = true := by
  quickRfl

theorem rel0 : rel.getD 0 [] = [0, 0, 0, 0, 0, 0, 0, 0] :=
  of_decide_eq_true (p := rel.getD 0 [] = [0, 0, 0, 0, 0, 0, 0, 0]) (by quickRfl)

theorem rel6 : rel.getD 6 [] = [1, 1, 0, 0, 0, 0, 0, 0] :=
  of_decide_eq_true (p := rel.getD 6 [] = [1, 1, 0, 0, 0, 0, 0, 0]) (by quickRfl)

theorem isUnit_of_pow {M : Type} [Monoid M] {x : M} {n : ℕ} (h : x ^ (n + 1) = 1) : IsUnit x :=
  ⟨⟨x, x ^ n, by rw [← pow_succ', h], by rw [← pow_succ, h]⟩, rfl⟩

theorem unitA : IsUnit (CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 1)) :=
  isUnit_of_pow (n := 1) omA_sq

theorem unitB : IsUnit (CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 2)) :=
  isUnit_of_pow (n := 2) omB_cube

theorem jfacts : ∃ R hs BW, JFacts (CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 1))
    (CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 2)) wr fus ce R hs BW
    (fun i => CFSG.KS.Ord.ordMat 5 9 13 117 (hwm.getD i.val 0)) :=
  chkJCl_sound CFSG.KD.FamHNSeed.consts consts9 cA cB unitA unitB rel0 rel6 chkJCl

theorem wfacts : ∃ D, WFacts (fun i => CFSG.KS.Ord.ordMat 5 9 13 117 (hwm.getD i.val 0))
    (vOf 9 c0) D fus oth :=
  chkW_sound chkW

theorem sporKRest_cover_JH :
    SporKRestCover 5 ↥JH := by
  have : Finite ↥JH := Finite.of_injective ρJ ρJ_injective
  obtain ⟨R, hs, BW, hJ⟩ := jfacts
  obtain ⟨D, hW⟩ := wfacts
  have ea : ρJ aJ = CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 1) :=
    (ρJ_apply aJ).trans matJ_aJ
  have eb : ρJ bJ = CFSG.KS.HNLocal.OM (CFSG.KD.FamHNSeed.RW 2) :=
    (ρJ_apply bJ).trans matJ_bJ
  rw [← ea, ← eb] at hJ
  obtain ⟨S₀, X, hp, hcomp, hgen⟩ := classes_of_facts ρJ ρJ_injective aJ bJ
    (m := 17473978368) (by rw [card_JH]; norm_num) (by norm_num) hJ hW
  refine sporKRest_cover_of_classes Nat.prime_five ((List.range 5).map X) ?_ ?_
  · intro s hs
    obtain ⟨k, hk, h⟩ := hcomp s hs
    exact ⟨X k, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, h⟩
  · intro r hr x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    obtain ⟨Z, hZ, ha, hb⟩ := hgen k (List.mem_range.mp hk)
    exact sporKRest_generating_of_pgroup_closure Nat.prime_five aJ bJ (closure_ab hnsData) S₀ hp
      (X k) Z hZ ha hb hx

theorem sporKRest_cover_HN_5_native :
    SporKRestCover 5 CFSG.Blueprint.NativeSporadic.HN :=
  @SporKRestCover.of_mulEquiv ↥JH CFSG.Blueprint.NativeSporadic.HN inferInstance inferInstance
    hnEquivJ.symm 5 sporKRest_cover_JH

end CertificateChecks.KernelHN1023016

end
