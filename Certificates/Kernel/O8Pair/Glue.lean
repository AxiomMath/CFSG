module

public import CFSG.Certificates.Kernel.O8PairSound
public import Certificates.Kernel.O8Pair.Chk
public import Certificates.Kernel.OmegaEight.Bridge3009
import CFSG.Certificates.Kernel.O8SASound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.GroupTheory.LocalCores.Fitting
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
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8P

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KC.O8P CFSG.EvenSmallLie.OmegaEight
open CFSG.ComponentClassification.RankTwoHypIICover.O8

theorem kRoot : allN 8 (fun k => actsK KernelO8.NSP KernelO8.NIP (KernelO8.AP.S k) (saAtK D.V k)) =
    true := by
  quickRfl

theorem blk {f : Nat → Bool} {b len : Nat} (h : allBlk b f len = true) {k : Nat} (h1 : b ≤ k)
    (h2 : k < b + len) : f k = true := by
  have e := CFSG.KS.allBlk_spec h (k - b) (by omega)
  have e2 : Nat.add b (k - b) = k := by change b + (k - b) = k; omega
  rwa [e2] at e

theorem slp_all : ∀ k < 14958, slp k = true := by
  intro k hk
  have b0 : allBlk 0 slp 2048 = true := kSlp_0
  have b1 : allBlk 2048 slp 2048 = true := kSlp_1
  have b2 : allBlk 4096 slp 2048 = true := kSlp_2
  have b3 : allBlk 6144 slp 2048 = true := kSlp_3
  have b4 : allBlk 8192 slp 2048 = true := kSlp_4
  have b5 : allBlk 10240 slp 2048 = true := kSlp_5
  have b6 : allBlk 12288 slp 2048 = true := kSlp_6
  have b7 : allBlk 14336 slp 622 = true := kSlp_7
  rcases (by omega : k < 2048 ∨ (2048 ≤ k ∧ k < 4096) ∨ (4096 ≤ k ∧ k < 6144) ∨
    (6144 ≤ k ∧ k < 8192) ∨ (8192 ≤ k ∧ k < 10240) ∨ (10240 ≤ k ∧ k < 12288) ∨
    (12288 ≤ k ∧ k < 14336) ∨ 14336 ≤ k) with h | h | h | h | h | h | h | h
  · exact blk b0 (by omega) (by omega)
  · exact blk b1 (by omega) (by omega)
  · exact blk b2 (by omega) (by omega)
  · exact blk b3 (by omega) (by omega)
  · exact blk b4 (by omega) (by omega)
  · exact blk b5 (by omega) (by omega)
  · exact blk b6 (by omega) (by omega)
  · exact blk b7 (by omega) (by omega)

theorem scan_all : ∀ i < 8192, scan i = true := by
  intro i hi
  have b0 : allBlk 0 scan 2048 = true := kScan_0
  have b1 : allBlk 2048 scan 2048 = true := kScan_1
  have b2 : allBlk 4096 scan 2048 = true := kScan_2
  have b3 : allBlk 6144 scan 2048 = true := kScan_3
  rcases (by omega : i < 2048 ∨ (2048 ≤ i ∧ i < 4096) ∨ (4096 ≤ i ∧ i < 6144) ∨ 6144 ≤ i) with
    h | h | h | h
  · exact blk b0 (by omega) (by omega)
  · exact blk b1 (by omega) (by omega)
  · exact blk b2 (by omega) (by omega)
  · exact blk b3 (by omega) (by omega)

theorem ent_all : ∀ q < 224, ent q = true := by
  intro q hq
  have b0 : allBlk 0 ent 32 = true := kEnt_0
  have b1 : allBlk 32 ent 32 = true := kEnt_1
  have b2 : allBlk 64 ent 32 = true := kEnt_2
  have b3 : allBlk 96 ent 32 = true := kEnt_3
  have b4 : allBlk 128 ent 32 = true := kEnt_4
  have b5 : allBlk 160 ent 32 = true := kEnt_5
  have b6 : allBlk 192 ent 32 = true := kEnt_6
  rcases (by omega : q < 32 ∨ (32 ≤ q ∧ q < 64) ∨ (64 ≤ q ∧ q < 96) ∨ (96 ≤ q ∧ q < 128) ∨
    (128 ≤ q ∧ q < 160) ∨ (160 ≤ q ∧ q < 192) ∨ 192 ≤ q) with h | h | h | h | h | h | h
  · exact blk b0 (by omega) (by omega)
  · exact blk b1 (by omega) (by omega)
  · exact blk b2 (by omega) (by omega)
  · exact blk b3 (by omega) (by omega)
  · exact blk b4 (by omega) (by omega)
  · exact blk b5 (by omega) (by omega)
  · exact blk b6 (by omega) (by omega)

theorem kIN : ∀ j < 38, repTypes.getD j 0 < 3 → f1 ET0.IN j = 1 := by decide +kernel

theorem facts : O8PairFacts := by
  have hNR : D.NR = 14958 := Nat.eq_of_beq_eq_true kNR
  have hNO : D.NO = 224 := Nat.eq_of_beq_eq_true kNO
  refine pairFacts_of_K (V := D.V) (A := D.A) (B := D.B) (CH := D.CH) (PO := D.PO) (NO := D.NO)
    (T := ET0) (fun k hk => ?_) rfl (fun k hk => ?_) rfl rfl kIN (CFSG.KS.allN_spec kChi)
    scan_all (fun q hq => ?_)
  · have h := CFSG.KS.allN_spec kRoot k hk
    rw [KernelO8.gen_get (by omega)]
    exact actsK_sound KernelO8.ns_bind KernelO8.ni_bind h
  · change k < D.NR at hk
    exact slp_all k (hNR ▸ hk)
  · exact ent_all q (hNO ▸ hq)

end CertificateChecks.KernelO8P

end
