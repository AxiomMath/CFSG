module

public import Certificates.Kernel.SporSch.Co1.GenK
public import Certificates.Kernel.SporSch.Co1.Split
public import CFSG.Certificates.Kernel.SporSch.Co1StabSound
public import CFSG.Certificates.Kernel.SporSch.Co1GenBSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Gen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch.Co1Elem CertificateChecks.KernelSporSch.Co1Split
open CertificateChecks.KernelSporSch.Co1ThreeLocal CertificateChecks.KernelSporSch.Co1Packed

theorem ext_eq : extInitRows = (List.range 10).map fun i => unpack 24 24 (ED.M i) := by
  have hm : ((List.range 10).map fun i => unpack 24 24 (ED.M i)) =
      (List.range 10).map fun i => unpack 24 24 (EI i) :=
    List.map_congr_left (fun i hi => by
      rw [Nat.eq_of_beq_eq_true (allN_spec kEI i (List.mem_range.1 hi))])
  rw [hm]
  unfold extInitRows
  rw [aRows_eq, c_eq 0 (by omega), c_eq 1 (by omega), gRows_eq, x_eq]
  rfl

theorem dag_eq : extDag = ((List.range ED.N).map fun i => unpack 24 24 (ED.M i),
    (List.range ED.N).map fun i => unpack 24 24 (ED.MI i), true) := by
  unfold extDag
  exact dagIK_sound ext_eq kD

theorem cols_eq : extColsT =
    Array.ofFn (n := 93) fun j => transposeRows 24 (unpack 24 24 (ED.M j.val)) := by
  unfold extColsT
  rw [dag_eq, Nat.eq_of_beq_eq_true kN]
  refine congrArg (Array.ofFn (n := 93)) (funext fun j => congrArg (transposeRows 24) ?_)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.2, Option.map_some,
    Option.getD_some]

theorem check : genCheck = true := by
  have h : genCheck = (extDag.2.2 && extDag.1.length == 93 &&
      genP extColsT Data.towerQuot Data.towerBase Data.towerGens Data.towerSizes) := by
    unfold genCheck genP fixOK fixOKP treeOK treeOKP towerTree Native.bfs bfsP stepV stepVP towerB towerQ
      towerJ towerN
    rfl
  rw [h, cols_eq, gen_sound (M := ED.M) ?_, dag_eq, Nat.eq_of_beq_eq_true kN]
  · simp
  · intro i hi
    interval_cases i
    · exact ⟨_, _, _, _, _, 512, TW.hd0, TW.hc0, TW.hn0, by decide, by decide, by decide, hl_of_tab TW.tb TW.hl0,
        TW.hp0, fq0, by decide, by decide⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd1, TW.hc1, TW.hn1, by decide, by decide, by decide, hl_of_tab TW.tb TW.hl1,
        TW.hp1, fq1, by decide, by decide⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd2, TW.hc2, TW.hn2, by decide, by decide, by decide, hl_of_tab TW.tb TW.hl2,
        TW.hp2, fq2, by decide, by decide⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd3, TW.hc3, TW.hn3, by decide, by decide, by decide, hl_of_tab TW.tb TW.hl3,
        TW.hp3, fq3, by decide, by decide⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd4, TW.hc4, TW.hn4, by decide, by decide, by decide, hl_of_tab TW.tb TW.hl4,
        TW.hp4, fq4, by decide, by decide⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd5, TW.hc5, TW.hn5, by decide, by decide, by decide, hl_of_tab TW.tb TW.hl5,
        TW.hp5, fq5, by decide, by decide⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd6, TW.hc6, TW.hn6, by decide, by decide, by decide, hl_of_tab TW.tb TW.hl6,
        TW.hp6, fq6, by decide, by decide⟩

end CertificateChecks.KernelSporSch.Co1Gen

end
