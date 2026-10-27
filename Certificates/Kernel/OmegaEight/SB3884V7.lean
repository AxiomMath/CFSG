module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884S7
public import Certificates.Kernel.OmegaEight.SB3873D6

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0

namespace V7

theorem hw : wOK 1 31 = true := by decide +kernel

theorem hl : lOK 1 = true := by decide +kernel

theorem hio : iotaOK (MK 1 31 24) 7 = true := by decide +kernel

theorem hI : kInv (MK 1 31 24) 131072 = invRows63.flatten :=
  kInv_of_partB ⟨by decide, fun s hs => by interval_cases s <;> decide +kernel⟩

theorem c0 : centOK3 (MK 1 31 24) (IK 1 31 24) t1Gens 131072 32 cent7_0 = true := by
  decide +kernel

theorem c1 : centOK3 (MK 1 31 24) (IK 1 31 24) t1Gens 131072 32 cent7_1 = true := by
  decide +kernel

theorem c2 : centOK3 (MK 1 31 24) (IK 1 31 24) t1Gens 131072 32 cent7_2 = true := by
  decide +kernel

theorem c3 : centOK3 (MK 1 31 24) (IK 1 31 24) t1Gens 131072 32 cent7_3 = true := by
  decide +kernel

theorem c4 : centOK3 (MK 1 31 24) (IK 1 31 24) t1Gens 131072 32 cent7_4 = true := by
  decide +kernel

theorem c5 : centOK3 (MK 1 31 24) (IK 1 31 24) t1Gens 131072 32 cent7_5 = true := by
  decide +kernel

theorem hc : (cents7.all (centOK3 (MK 1 31 24) (IK 1 31 24) t1Gens 131072 32)) = true := by
  simp only [cents7, List.all_cons, List.all_nil, Bool.and_true, c0, c1, c2, c3, c4, c5]

theorem h8l : (kRepsC (t1Cls 1 31 24) 8).length ≤ 4 * 4 := by decide +kernel

theorem h8 : ∀ s < 4, ((chunks 4 4 (kRepsC (t1Cls 1 31 24) 8)).getD s []).all
    (fun r => l2Like.contains r || kCount (MK 1 31 24) invRows63.flatten r != 1439) = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem hR : l2SurvR cents7 = true := by decide +kernel

theorem h16l : (kRepsC (t1Cls 1 31 24) 16).length ≤ 4 * 6 := by decide +kernel

theorem h16 : ∀ s < 6, ((chunks 4 6 (kRepsC (t1Cls 1 31 24) 16)).getD s []).all
    (fun r => recs7.any fun q => q.1 == r &&
      q.2 == (recM (MK 1 31 24) (IK 1 31 24) t1Gens r).map Prod.fst) = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem hF : ∀ e ∈ s2Canon.getD 7 [], wAOK e.1 e.2.1 = true ∧ lOK e.1 = true := by
  decide +kernel

theorem hA : ((s2Canon.getD 7 []).all fun e =>
    l2ActK (MK 1 31 24) (IoK (MK 1 31 24) 7) (FAK e.1 e.2.1) e.2.2.1 e.2.2.2 recs7 &&
      l2ActK (MK 1 31 24) (IoK (MK 1 31 24) 7) (FAK e.1 e.2.1) e.2.2.1 (MK 1 31 24 e.2.2.2 24)
        recs7) = true := by
  decide +kernel

end V7

open V7 in
theorem survAct7 : l2SurvActOK 7 invRows63.flatten cents7 recs7 = true :=
  l2SurvActOK_of (k := 1) (m := 31) (z := 24) rfl rfl rfl hw hl hio
    (l2SurvOK_of (k := 1) (m := 31) (z := 24) rfl rfl rfl hw hl hI
      (l2SurvK_of hc h8l h8 hR h16l h16)) hF hA

end CertificateChecks.KernelO8.SB3884

end
