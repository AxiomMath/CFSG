module

public import Certificates.Kernel.OmegaEight.SB3884
public import Certificates.Kernel.OmegaEight.SB3884S4
public import Certificates.Kernel.OmegaEight.SB3873D3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

set_option maxHeartbeats 0

namespace V4

theorem hw : wOK 1 16 = true := by decide +kernel

theorem hl : lOK 1 = true := by decide +kernel

theorem hio : iotaOK (MK 1 16 24) 4 = true := by decide +kernel

theorem hI : kInv (MK 1 16 24) 131072 = invRows33.flatten :=
  kInv_of_partB ⟨by decide, fun s hs => by interval_cases s <;> decide +kernel⟩

theorem c0 : centOK3 (MK 1 16 24) (IK 1 16 24) t1Gens 131072 32 cent4_0 = true := by
  decide +kernel

theorem c1 : centOK3 (MK 1 16 24) (IK 1 16 24) t1Gens 131072 32 cent4_1 = true := by
  decide +kernel

theorem c2 : centOK3 (MK 1 16 24) (IK 1 16 24) t1Gens 131072 32 cent4_2 = true := by
  decide +kernel

theorem c3 : centOK3 (MK 1 16 24) (IK 1 16 24) t1Gens 131072 32 cent4_3 = true := by
  decide +kernel

theorem c4 : centOK3 (MK 1 16 24) (IK 1 16 24) t1Gens 131072 32 cent4_4 = true := by
  decide +kernel

theorem c5 : centOK3 (MK 1 16 24) (IK 1 16 24) t1Gens 131072 32 cent4_5 = true := by
  decide +kernel

theorem hc : (cents4.all (centOK3 (MK 1 16 24) (IK 1 16 24) t1Gens 131072 32)) = true := by
  simp only [cents4, List.all_cons, List.all_nil, Bool.and_true, c0, c1, c2, c3, c4, c5]

theorem h8l : (kRepsC (t1Cls 1 16 24) 8).length ≤ 4 * 4 := by decide +kernel

theorem h8 : ∀ s < 4, ((chunks 4 4 (kRepsC (t1Cls 1 16 24) 8)).getD s []).all
    (fun r => l2Like.contains r || kCount (MK 1 16 24) invRows33.flatten r != 1439) = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem hR : l2SurvR cents4 = true := by decide +kernel

theorem h16l : (kRepsC (t1Cls 1 16 24) 16).length ≤ 4 * 6 := by decide +kernel

theorem h16 : ∀ s < 6, ((chunks 4 6 (kRepsC (t1Cls 1 16 24) 16)).getD s []).all
    (fun r => recs4.any fun q => q.1 == r &&
      q.2 == (recM (MK 1 16 24) (IK 1 16 24) t1Gens r).map Prod.fst) = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem hF : ∀ e ∈ s2Canon.getD 4 [], wAOK e.1 e.2.1 = true ∧ lOK e.1 = true := by
  decide +kernel

theorem hA : ((s2Canon.getD 4 []).all fun e =>
    l2ActK (MK 1 16 24) (IoK (MK 1 16 24) 4) (FAK e.1 e.2.1) e.2.2.1 e.2.2.2 recs4 &&
      l2ActK (MK 1 16 24) (IoK (MK 1 16 24) 4) (FAK e.1 e.2.1) e.2.2.1 (MK 1 16 24 e.2.2.2 24)
        recs4) = true := by
  decide +kernel

end V4

open V4 in
theorem survAct4 : l2SurvActOK 4 invRows33.flatten cents4 recs4 = true :=
  l2SurvActOK_of (k := 1) (m := 16) (z := 24) rfl rfl rfl hw hl hio
    (l2SurvOK_of (k := 1) (m := 16) (z := 24) rfl rfl rfl hw hl hI
      (l2SurvK_of hc h8l h8 hR h16l h16)) hF hA

end CertificateChecks.KernelO8.SB3884

end
