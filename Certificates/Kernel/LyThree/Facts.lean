module

public import Certificates.Kernel.LyThree.ChecksA
public import Certificates.Kernel.LyThree.ChecksB
public import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.Certificates.Kernel.SlpClsSound
public import CFSG.Sporadic.Ly.Setup
public import CFSG.Certificates.Kernel.Orders.Ly.Checks.K
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses
public import CFSG.Sporadic.Recognition.LyonsAS44Cert
public import CFSG.Sporadic.Recognition.LyonsAS4Quot
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux
public import CFSG.Sporadic.Suz.Setup
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.GH74.Generic.Certificates
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestNative
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Recognition.LyonsAS44Quat
public import CFSG.Sporadic.Recognition.LyonsLocalEdge
public import CFSG.Sporadic.Schreier.J4SThree
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base
public import Certificates.Certificate3085Base

public section

namespace CertificateChecks.KernelLyThree

open CFSG.Sporadic.Ly CFSG.KS.Ord CFSG.KS.SlpCls CFSG.StandardType.SporadicShape
open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.Sporadic.Recognition.LyonsSims
open CertificateChecks.KernelSporSch

noncomputable def ρL [LySeed] : J →* Matrix (Fin 111) (Fin 111) (ZMod 5) where
  toFun := mat
  map_one' := mat_one
  map_mul' := mat_mul

theorem ρL_injective [LySeed] : Function.Injective ρL := mat_injective

theorem toMat_U (X : ℕ) : CFSG.Sporadic.He.Native.toMat 5 111
    (CFSG.KS.SporSch.LyM.unpackL 111 12 1332 X) = ordMat 5 111 12 1332 X := by
  ext i j
  rw [CFSG.Sporadic.He.Native.toMat_apply, CFSG.KS.SporSch.LyM.unpackL_get i.isLt j.isLt]
  unfold ordMat
  rfl

theorem ρL_a [LySeed] : ρL CFSG.Sporadic.Ly.a = ordMat 5 111 12 1332 LyBS.A := by
  change mat CFSG.Sporadic.Ly.a = _
  rw [mat_a, ← toMat_matA, LyBSF.matA_eq, toMat_U]

theorem ρL_b [LySeed] : ρL CFSG.Sporadic.Ly.b = ordMat 5 111 12 1332 LyBS.B := by
  change mat CFSG.Sporadic.Ly.b = _
  rw [mat_b, ← toMat_matB, LyBSF.matB_eq, toMat_U]

theorem cA : Canon 5 111 12 LyBS.A := validM_canon CFSG.KD.OrdLy.consts (LyBSF.hv LyBS.vA)

theorem cB : Canon 5 111 12 LyBS.B := validM_canon CFSG.KD.OrdLy.consts (LyBSF.hv LyBS.vB)

theorem factsA : ∃ R, ClsFacts (ordMat 5 111 12 1332 LyBS.A) (ordMat 5 111 12 1332 LyBS.B) 3 1 1
    CFSG.KD.LyThree.rxA CFSG.KD.LyThree.sgA CFSG.KD.LyThree.tbA CFSG.KD.LyThree.cbA
    CFSG.KD.LyThree.entA R :=
  clsL_sound CFSG.KD.OrdLy.consts (by norm_num) (by norm_num) (by norm_num) cA cB
    CFSG.KD.LyThree.chkA

theorem factsB : ∃ R, ClsFacts (ordMat 5 111 12 1332 LyBS.A) (ordMat 5 111 12 1332 LyBS.B) 3 2 3
    CFSG.KD.LyThree.rxB CFSG.KD.LyThree.sgB CFSG.KD.LyThree.tbB CFSG.KD.LyThree.cbB
    CFSG.KD.LyThree.entB R :=
  clsL_sound CFSG.KD.OrdLy.consts (by norm_num) (by norm_num) (by norm_num) cA cB
    CFSG.KD.LyThree.chkB

theorem trace_conj {G : Type} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) (ZMod 5))
    {x y : G} (h : IsConj x y) : (ρ y).trace = (ρ x).trace := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  rw [map_mul, map_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← map_mul, inv_mul_cancel,
    map_one, Matrix.one_mul]

theorem two_classes [LySeed] : ∃ xA xB : J, orderOf xA = 3 ∧ orderOf xB = 3 ∧ ¬ IsConj xA xB ∧
    (∀ x : J, IsConj xA x → SporKRestGenerating 3 x) ∧
    (∀ x : J, IsConj xB x → SporKRestGenerating 3 x) := by
  have : Finite J := Finite.of_injective _ ρL_injective
  obtain ⟨RA, hA⟩ := factsA
  obtain ⟨RB, hB⟩ := factsB
  rw [← ρL_a, ← ρL_b] at hA hB
  obtain ⟨xA, eA, oA, gA⟩ := generating_of_clsFacts ρL ρL_injective Nat.prime_three _ _ closure_ab hA
  obtain ⟨xB, eB, oB, gB⟩ := generating_of_clsFacts ρL ρL_injective Nat.prime_three _ _ closure_ab hB
  refine ⟨xA, xB, oA, oB, fun hc => ?_, gA, gB⟩
  have h := trace_conj ρL hc
  rw [eA, eB, hA.tr, hB.tr] at h
  exact absurd h (by decide)

theorem pick {K : Type} [Group K] {xA xB u v y : K} (hnc : ¬ IsConj xA xB)
    (hA : IsConj xA u ∨ IsConj xA v) (hB : IsConj xB u ∨ IsConj xB v)
    (hy : IsConj y u ∨ IsConj y v) : IsConj xA y ∨ IsConj xB y := by
  rcases hA with h1 | h1 <;> rcases hB with h2 | h2 <;> rcases hy with h3 | h3 <;>
    first
    | exact absurd (h1.trans h2.symm) hnc
    | exact Or.inl (h1.trans h3.symm)
    | exact Or.inr (h2.trans h3.symm)

theorem cover_J :
    SporKRestCover 3 J := by
  obtain ⟨xA, xB, oA, oB, hnc, gA, gB⟩ := two_classes
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover
    (LyMult.oneClassDoubleCover_of_ly (T := J) ⟨lyEquivJ.symm⟩)
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  have hcl := (lemma45_classes_of_certificate D S).1
  refine sporKRest_cover_of_classes Nat.prime_three [xA, xB] (fun s hs => ?_) ?_
  · rcases pick hnc (hcl xA oA) (hcl xB oB) (hcl s hs) with h | h
    · exact ⟨xA, List.mem_cons_self, h⟩
    · exact ⟨xB, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
  · intro r hr x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact gA x hx
    · exact gB x hx

theorem cover_native :
    SporKRestCover 3 CFSG.Blueprint.NativeSporadic.Ly :=
  @SporKRestCover.of_mulEquiv J CFSG.Blueprint.NativeSporadic.Ly inferInstance inferInstance
    lyEquivJ.symm 3 cover_J

end CertificateChecks.KernelLyThree

end
