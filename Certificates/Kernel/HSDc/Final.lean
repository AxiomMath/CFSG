module

public import Certificates.Kernel.HSDc.Checks
public import Certificates.Kernel.HSDc.C0
public import Certificates.Kernel.HSDc.C1
public import Certificates.Kernel.HSDc.C2
public import Certificates.Kernel.HSDc.C3
public import Certificates.Kernel.LocalQT.HS4089.G
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDcInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.SporSch.J4S.NoCP

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HSDc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.PcW
open CFSG.Sporadic.HS.Native (hsData)

theorem rc_len : D.Rc.length = 8 := rfl

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  rw [rc_len, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact K0.all 0 (by decide)
  · exact K0.all 1 (by decide)
  · exact K1.all 0 (by decide)
  · exact K1.all 1 (by decide)
  · exact K2.all 0 (by decide)
  · exact K2.all 1 (by decide)
  · exact K3.all 0 (by decide)
  · exact K3.all 1 (by decide)

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks]
  rfl

theorem lcB : ((List.range 8).all fun l =>
    J.lc.getD l 0 == CFSG.KD.LQT.H4089S.TF (nodes.getD l 0)) = true := by
  quickRfl

theorem nodes_lt : ∀ l < 8, nodes.getD l 0 < 219 := by decide

theorem ltB : ((List.range 8).all fun l => (List.range 1100).all fun p => Nat.blt (C.L l p) 1100) =
    true := by
  quickRfl

theorem nodes_ok : ∀ l < 8, ∀ p < hsData.n,
    (hsSLP[nodes.getD l 0]!).getD p 0 = C.L l p ∧ C.L l p < hsData.n := by
  intro l hl
  have hr := CFSG.KD.LQT.H4089.rep_nodes (nodes.getD l 0) (nodes_lt l hl)
  have hc : J.lc.getD l 0 = CFSG.KD.LQT.H4089S.TF (nodes.getD l 0) :=
    eq_of_beq (List.all_eq_true.1 lcB l (List.mem_range.2 hl))
  have hL : ∀ p, C.L l p = CFSG.KC.Enum.pg 11 (CFSG.KS.mask 11)
      (CFSG.KD.LQT.H4089S.TF (nodes.getD l 0)) p := by
    intro p
    change CFSG.KC.LQT.PW.imgW 11 (J.lc.getD l 0) p = _
    rw [hc]
    rfl
  have hn : hsData.n = 1100 := rfl
  intro p hp
  rw [hn] at hp ⊢
  refine ⟨?_, ?_⟩
  · rw [hL, ← rep_get hr p hp, Array.getElem!_eq_getD]
    rfl
  · have h1 := List.all_eq_true.1 (List.all_eq_true.1 ltB l (List.mem_range.2 hl)) p
      (List.mem_range.2 hp)
    simpa using h1

theorem omB : (hsLatK.Om.map (fun o => o.lbl.size) == #[1, 15, 21, 3, 3]) = true := by
  quickRfl

theorem otB : (hsOtK.map (fun o => o.lbl.size) == #[1, 8, 8, 2, 2]) = true := by
  quickRfl

theorem facts : HSDcFacts :=
  ⟨dc_ok, invs, nodes_ok, eq_of_beq sepB, mws, Nat.eq_of_beq_eq_true mwLenB, eq_of_beq mw0B,
    eq_of_beq omB, mems, eq_of_beq otB⟩

end CFSG.KD.HSDc

end
