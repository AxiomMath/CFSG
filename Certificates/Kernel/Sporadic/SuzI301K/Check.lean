module

public import Certificates.Kernel.Sporadic.SuzI301K.GlueCent
public import Certificates.Kernel.Sporadic.SuzI301K.GlueFix

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KC.LinRepSound CFSG.KC.LinRepCheck CFSG.KC.SuzI301Lin
open CFSG.KC.SuzI301K CFSG.KD.SuzI301 CFSG.PSL3Four.Native CFSG.Sporadic.SuzI301
  CFSG.ComponentClassification.AS81.SuzB0

theorem enum_inv_facts :
    enumOK 64 (matTabs.push (mat64 (sTau ()))) (enumBFS 64 (matTabs.push (mat64 (sTau ()))) 51840) =
        true ∧
      ((enumBFS 64 (matTabs.push (mat64 (sTau ()))) 51840).tabs.size == 51840) = true ∧
      allBelow (enumBFS 64 (matTabs.push (mat64 (sTau ()))) 51840).tabs.size
        (fun k => invTest HLt (enumBFS 64 (matTabs.push (mat64 (sTau ()))) 51840).tabs[k]!) = true := by
  have e : mat64 (sTau ()) = linTab mT := mat64_T
  rw [e]
  obtain ⟨h1, h2, h3⟩ := enum_facts
  refine ⟨h1, by rw [h2]; rfl, allBelow_true fun k hk => ?_⟩
  rw [h2] at hk
  rw [h3 k hk]
  exact inv_facts k hk

theorem suzCheck_true : suzCheck () = true := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19,
    d20, d21, d22⟩ := deg_facts
  obtain ⟨c1, c2, c3, c4⟩ := coords_facts
  obtain ⟨v1, v2, v3, v4⟩ := valid64_facts
  obtain ⟨e1, e2, e3⟩ := enum_inv_facts
  unfold suzCheck
  simp only [Bool.and_eq_true, and_assoc]
  exact ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19,
    d20, d21, d22, c1, c2, c3, c4, v1, v2, v3, v4, hl_cube, e1, e2, e3, notIn_facts, cent_facts,
    fix_facts, form_facts, count_facts⟩

end CertificateChecks.KernelSpor.SuzI301K

end
