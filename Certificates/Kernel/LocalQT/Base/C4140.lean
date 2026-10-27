module

public import CFSG.Certificates.Kernel.LocalQTBaseWSound
public import CFSG.Certificates.Kernel.SporSch.RuVOrbSound
public import Certificates.Kernel.VecCert.HS
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.HS
public import Certificates.Certificate113

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.LQT.C4140

open CFSG.KC.VecK CFSG.KC.LQT.BW CFSG.QuasithinUnique.K1.SporadicPerm CertificateChecks.KernelVec.HS
open CFSG.Sporadic.HS.Native (hsData)

theorem seed : seedK csA csB 20 MA MB NA NB 2 5 = true := by quickRfl

theorem p0 : Nat.beq (lk Pt 32 0) 175 = true := by quickRfl

theorem horb : ∀ h < (hsData ()).n,
    orbAt (hsData ()).d (hsData ()).n NA NB Pt AT BT h = true := by
  refine allS_cover (ns := 5) (S := 256) (fun s hs => ?_) (by decide)
  interval_cases s
  exacts [orb_0, orb_1, orb_2, orb_3, orb_4]

theorem hbfs : ∀ h < (hsData ()).n, bfsAt (hsData ()).n AT BT FO h = true := by
  refine allS_cover (ns := 5) (S := 256) (fun s hs => ?_) (by decide)
  interval_cases s
  exacts [bfs_0, bfs_1, bfs_2, bfs_3, bfs_4]

theorem hsort : ∀ h < (hsData ()).n, sortAt (hsData ()).n Pt S IP SP h = true := by
  refine allS_cover (ns := 5) (S := 256) (fun s hs => ?_) (by decide)
  interval_cases s
  exacts [sort_0, sort_1, sort_2, sort_3, sort_4]

theorem tables : ∀ i < 1100,
    CFSG.Sporadic.Th.Native.ap (hsData.orbit ()).alpha i = lk AT 32 i ∧
      CFSG.Sporadic.Th.Native.ap (hsData.orbit ()).beta i = lk BT 32 i :=
  vOrbit_tables (hsData ()) hA hB seed (by quickRfl) p0 horb hbfs hsort

@[expose] noncomputable def ta : List Nat := (List.range 1100).map (lk AT 32)

@[expose] noncomputable def tb : List Nat := (List.range 1100).map (lk BT 32)

theorem n_eq : (hsData ()).n = 1100 := rfl

theorem ta_eq : hsTa = ta.toArray := by
  unfold hsTa ta
  rw [n_eq]
  congr 1
  exact List.map_congr_left fun i hi => (tables i (List.mem_range.1 hi)).1

theorem tb_eq : hsTb = tb.toArray := by
  unfold hsTb tb
  rw [n_eq]
  congr 1
  exact List.map_congr_left fun i hi => (tables i (List.mem_range.1 hi)).2

theorem valid : slpValidAux hsProg 2 = true := by quickRfl

theorem bk : baseWK 1100 11 hsB ta tb hsProg hsQp 164 202 206 204 208 9 100000 512 = true := by
  quickRfl

theorem cert : BaseCertS (hsData ()).n hsB hsSLP hsQp 164 202 206 204 208
    hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 := by
  have h := baseW_sound (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ _ bk
  rw [← ta_eq, ← tb_eq] at h
  exact h

end CFSG.KD.LQT.C4140

end
