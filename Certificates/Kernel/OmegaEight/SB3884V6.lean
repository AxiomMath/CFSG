module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884S6
public import Certificates.Kernel.OmegaEight.SB3873D5

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0

namespace V6

theorem hw : wOK 1 26 = true := by decide +kernel

theorem hl : lOK 1 = true := by decide +kernel

theorem hio : iotaOK (MK 1 26 24) 6 = true := by decide +kernel

theorem hI : kInv (MK 1 26 24) 131072 = invRows53.flatten :=
  kInv_of_partB ⟨by decide, fun s hs => by interval_cases s <;> decide +kernel⟩

theorem c0 : centOK3 (MK 1 26 24) (IK 1 26 24) t1Gens 131072 32 cent6_0 = true := by
  decide +kernel

theorem c1 : centOK3 (MK 1 26 24) (IK 1 26 24) t1Gens 131072 32 cent6_1 = true := by
  decide +kernel

theorem c2 : centOK3 (MK 1 26 24) (IK 1 26 24) t1Gens 131072 32 cent6_2 = true := by
  decide +kernel

theorem c3 : centOK3 (MK 1 26 24) (IK 1 26 24) t1Gens 131072 32 cent6_3 = true := by
  decide +kernel

theorem c4 : centOK3 (MK 1 26 24) (IK 1 26 24) t1Gens 131072 32 cent6_4 = true := by
  decide +kernel

theorem c5 : centOK3 (MK 1 26 24) (IK 1 26 24) t1Gens 131072 32 cent6_5 = true := by
  decide +kernel

theorem hc : (cents6.all (centOK3 (MK 1 26 24) (IK 1 26 24) t1Gens 131072 32)) = true := by
  simp only [cents6, List.all_cons, List.all_nil, Bool.and_true, c0, c1, c2, c3, c4, c5]

theorem h8l : (kRepsC (t1Cls 1 26 24) 8).length ≤ 4 * 4 := by decide +kernel

theorem h8 : ∀ s < 4, ((chunks 4 4 (kRepsC (t1Cls 1 26 24) 8)).getD s []).all
    (fun r => l2Like.contains r || kCount (MK 1 26 24) invRows53.flatten r != 1439) = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem hR : l2SurvR cents6 = true := by decide +kernel

theorem h16l : (kRepsC (t1Cls 1 26 24) 16).length ≤ 4 * 6 := by decide +kernel

theorem h16 : ∀ s < 6, ((chunks 4 6 (kRepsC (t1Cls 1 26 24) 16)).getD s []).all
    (fun r => recs6.any fun q => q.1 == r &&
      q.2 == (recM (MK 1 26 24) (IK 1 26 24) t1Gens r).map Prod.fst) = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem hF : ∀ e ∈ s2Canon.getD 6 [], wAOK e.1 e.2.1 = true ∧ lOK e.1 = true := by
  decide +kernel

theorem hA : ((s2Canon.getD 6 []).all fun e =>
    l2ActK (MK 1 26 24) (IoK (MK 1 26 24) 6) (FAK e.1 e.2.1) e.2.2.1 e.2.2.2 recs6 &&
      l2ActK (MK 1 26 24) (IoK (MK 1 26 24) 6) (FAK e.1 e.2.1) e.2.2.1 (MK 1 26 24 e.2.2.2 24)
        recs6) = true := by
  decide +kernel

end V6

open V6 in
theorem survAct6 : l2SurvActOK 6 invRows53.flatten cents6 recs6 = true :=
  l2SurvActOK_of (k := 1) (m := 26) (z := 24) rfl rfl rfl hw hl hio
    (l2SurvOK_of (k := 1) (m := 26) (z := 24) rfl rfl rfl hw hl hI
      (l2SurvK_of hc h8l h8 hR h16l h16)) hF hA

end CertificateChecks.KernelO8.SB3884

end
