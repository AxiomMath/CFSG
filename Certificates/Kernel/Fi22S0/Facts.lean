
module

public import Certificates.Kernel.Fi22S0.Slp0
public import Certificates.Kernel.Fi22S0.Slp1
public import Certificates.Kernel.Fi22S0.Slp2
public import Certificates.Kernel.Fi22S0.Slp3
public import Certificates.Kernel.Fi22S0.Slp4
public import Certificates.Kernel.Fi22S0.Slp5
public import Certificates.Kernel.Fi22S0.Slp6
public import Certificates.Kernel.Fi22S0.Slp7
public import Certificates.Kernel.Fi22S0.Slp8
public import Certificates.Kernel.Fi22S0.Slp9
public import Certificates.Kernel.Fi22S0.Slp10
public import Certificates.Kernel.Fi22S0.Slp11
public import Certificates.Kernel.Fi22S0.Slp12
public import Certificates.Kernel.Fi22S0.Slp13
public import Certificates.Kernel.Fi22S0.Slp14
public import Certificates.Kernel.Fi22S0.Slp15
public import Certificates.Kernel.Fi22S0.Slp16
public import Certificates.Kernel.Fi22S0.Slp17
public import Certificates.Kernel.Fi22S0.Slp18
public import Certificates.Kernel.Fi22S0.Tabs
public import Certificates.Kernel.Fi22S0.Kill
public import Certificates.Kernel.Fi22S0.KillB
public import Certificates.Kernel.Fi22S0.ParseEq
public import Certificates.Kernel.SporCovBase.Fi22GlueBase
public import CFSG.Certificates.Kernel.Fi22S0.Glue
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.Common.ForallTreeFrom
public import Certificates.Data.CFSGNative.Fi22.Certificate
public import CFSG.Certificates.Kernel.Fi22S0.KillSound
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.StandardType.GGSporKRestDistinct
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CertificateChecks.KernelFi22S0

open CFSG.KC.Fi22S0 CFSG.KD.Fi22S0 CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27

#kc_forall_tree_from slpAll (fun k => ch131101slp k = true) 3 567
  CertificateChecks.KernelFi22S0.ch131101slp

#kc_forall_tree treeAll (fun q => ch131101tree q = true) 9 CertificateChecks.KernelFi22S0.ch131101tree

#kc_forall_tree leftAll (fun q => ch131101left q = true) 9 CertificateChecks.KernelFi22S0.ch131101left

#kc_forall_tree sortAll (fun q => ch131101sort q = true) 9 CertificateChecks.KernelFi22S0.ch131101sort

#kc_forall_tree killAll (fun q => ch131101kill q = true) 9 CertificateChecks.KernelFi22S0.ch131101kill

#kc_forall_tree repAll (fun q => ch131101rep q = true) 9 CertificateChecks.KernelFi22S0.ch131101rep

theorem blk_all {b m : ℕ} (hb : 0 < b) {f : ℕ → Bool} (h : ∀ q < m, blkC b f q = true) :
    ∀ i < b * m, f i = true := by
  intro i hi
  have hq : i / b < m := by
    rw [Nat.div_lt_iff_lt_mul hb]
    rw [Nat.mul_comm] at hi
    exact hi
  have hk := h (i / b) hq
  unfold blkC at hk
  have := CFSG.KS.allN_spec hk (i % b) (Nat.mod_lt _ hb)
  have e : Nat.add (Nat.mul b (i / b)) (i % b) = i := Nat.div_add_mod i b
  rw [e] at this
  exact this

theorem regAll : ∀ k, 3 ≤ k → k < 570 → regC RF oi oj k = true := by
  intro k h1 h2
  have h : ch131101slp (3 + (k - 3)) = true := slpAll (k - 3) (show k - 3 < 567 by omega)
  rw [show 3 + (k - 3) = k by omega] at h
  exact h

theorem oiAll : ∀ k, 3 ≤ k → k < 570 → oi k < k ∧ oj k < k := by
  intro k h1 h2
  have h := regAll k h1 h2
  unfold regC at h
  simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at h
  exact ⟨h.1, h.2.1⟩

theorem opsAll : ∀ k, 3 ≤ k → k < 570 → ((ops ())[k - 3]!).1 = oi k ∧ ((ops ())[k - 3]!).2 = oj k := by
  intro k h1 h2
  rw [ops_eq, CFSG.KS.LyS0K.ofFnG (fun t => (oi (t + 3), oj (t + 3))) (by omega : k - 3 < 567),
    Nat.sub_add_cancel h1]
  exact ⟨rfl, rfl⟩

theorem parAll : ∀ i < nS, 0 < i → ((par ())[i]!).1 = pp i ∧ ((par ())[i]!).2 = pj i := by
  intro i hi _
  rw [par_eq, CFSG.KS.LyS0K.ofFnG (fun i => (pp i, pj i)) (by unfold nS at hi; exact hi)]
  exact ⟨rfl, rfl⟩

theorem LAll : ∀ j < 3, ∀ i < nS, ((L ())[j]!)[i]! = lt j i := by
  intro j hj i hi
  rw [L_eq, CFSG.KS.LyS0K.ofFnG (fun j => Array.ofFn (n := 19683) fun i => lt j i.val) hj,
    CFSG.KS.LyS0K.ofFnG (fun i => lt j i) (by unfold nS at hi; exact hi)]

theorem k0_eq : k0 = pk5 bp := by decide

theorem gRAll : ∀ j < 3, RepE (gR j) (CFSG.HardMathSupport.Foote.E27.Fi22S0.gJ j) :=
  fun _ hj => rep_gR (rep_reg (A := CFSG.Sporadic.Fi22.Native.orbEntry 0)
    (B := CFSG.Sporadic.Fi22.Native.orbEntry 1)
    (fun x hx => CFSG.KD.SporCovBase.Fi22.hA x hx) (fun x hx => CFSG.KD.SporCovBase.Fi22.hB x hx)
    ch131101base_eq regAll opsAll) hj

theorem tabDataK : TabData CFSG.HardMathSupport.Foote.E27.Fi22S0.gJ par L nS 3 :=
  tabData_of gRAll k0_eq (blk_all (by norm_num) treeAll)
    (fun j hj i hi => CFSG.KS.allN_spec (blk_all (b := 2187) (m := 9) (by norm_num) leftAll i hi) j hj)
    (blk_all (by norm_num) sortAll) parAll LAll

theorem fi22S0Check_true : fi22S0Check () = true := by
  have hT := tabDataK
  have htree : ∀ i < 19683, 0 < i → pp i < i ∧ pj i < 3 := by
    intro i hi hpos
    have h := hT.par_lt i hpos hi
    obtain ⟨e1, e2⟩ := parAll i hi hpos
    rw [e1, e2] at h
    exact h
  exact fi22S0Check_of (shapeOK_of ops_eq oiAll par_eq htree L_eq) hT
    (killOK_of hT par_eq L_eq (blk_all (by norm_num) killAll) (blk_all (by norm_num) repAll))

end CertificateChecks.KernelFi22S0

end
