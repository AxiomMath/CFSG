module

public import Certificates.Kernel.M24L2.L2
public import Certificates.Kernel.M24L2.L5Check
public import Certificates.Kernel.M24L2.L5FbCheck
public import Certificates.Kernel.M24L2.L5FcCheck
public import CFSG.Certificates.Kernel.M24L2.L5Sound

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2 CFSG.CGT.M24R CFSG.CGT.L5R

theorem dmK_all : ∀ k < 20, dmK k = true := by
  intro k hk
  interval_cases k
  exacts [dmK0, dmK1, dmK2, dmK3, dmK4, dmK5, dmK6, dmK7, dmK8, dmK9, dmK10, dmK11, dmK12, dmK13,
    dmK14, dmK15, dmK16, dmK17, dmK18, dmK19]

theorem faLK_all : ∀ k < 20, faLK k = true := by
  intro k hk
  interval_cases k
  exacts [faLK0, faLK1, faLK2, faLK3, faLK4, faLK5, faLK6, faLK7, faLK8, faLK9, faLK10, faLK11,
    faLK12, faLK13, faLK14, faLK15, faLK16, faLK17, faLK18, faLK19]

theorem cdAK_all : ∀ k < 20, cdAK k = true := by
  intro k hk
  interval_cases k
  exacts [cdAK0, cdAK1, cdAK2, cdAK3, cdAK4, cdAK5, cdAK6, cdAK7, cdAK8, cdAK9, cdAK10, cdAK11,
    cdAK12, cdAK13, cdAK14, cdAK15, cdAK16, cdAK17, cdAK18, cdAK19]

theorem cdBK_all : ∀ k < 20, cdBK k = true := by
  intro k hk
  interval_cases k
  exacts [cdBK0, cdBK1, cdBK2, cdBK3, cdBK4, cdBK5, cdBK6, cdBK7, cdBK8, cdBK9, cdBK10, cdBK11,
    cdBK12, cdBK13, cdBK14, cdBK15, cdBK16, cdBK17, cdBK18, cdBK19]

theorem s0K_all : ∀ k < 20, s0K k = true := by
  intro k hk
  interval_cases k
  exacts [s0K0, s0K1, s0K2, s0K3, s0K4, s0K5, s0K6, s0K7, s0K8, s0K9, s0K10, s0K11, s0K12, s0K13,
    s0K14, s0K15, s0K16, s0K17, s0K18, s0K19]

theorem s1K_all : ∀ k < 20, s1K k = true := by
  intro k hk
  interval_cases k
  exacts [s1K0, s1K1, s1K2, s1K3, s1K4, s1K5, s1K6, s1K7, s1K8, s1K9, s1K10, s1K11, s1K12, s1K13,
    s1K14, s1K15, s1K16, s1K17, s1K18, s1K19]

theorem l5_facts : bCheckL (mkCtx ()) = true ∧ faCheckL (mkCtx ()) = true ∧
    fbCheckL (mkCtx ()) (betaT 0) true = true ∧ fbCheckL (mkCtx ()) gamT false = true ∧
    dCheckL (mkCtx ()) = true ∧ wCheckL (mkCtx ()) = true ∧ fcCheckL (mkCtx ()) = true := by
  obtain ⟨hR, -, hL, -⟩ := reach
  have hGL := mask_contains invK_all tree_ok
  have hG : ∀ n, validK glMask n = true → n ∈ (mkCtx ()).codes := fun n h =>
    mem_of_validK hR hGL h
  refine ⟨bCheckL_eq ▸ bL_ok, ?_, ?_, ?_, ?_, wCheckL_eq ▸ wL_ok, ?_⟩
  · exact faCheckL_of hR hL hG (slices_glL (Q := faLM glMask faW1 faW2)
      (F := sliceL (faLM glMask faW1 faW2)) (fun E h => sliceSpec h) faLK_all)
  · have h := fbCheckL_of hR hL hG (betaC_lt 0) (slices_glL (Q := candM (betaC 0) cands1)
      (F := sliceL (candM (betaC 0) cands1)) (fun E h => sliceSpec h) cdAK_all) fbL1_ok
    rw [← betaT_eq] at h
    exact h
  · have h := fbCheckL_of hR hL hG gamC_lt (slices_glL (Q := candM gamC cands2)
      (F := sliceL (candM gamC cands2)) (fun E h => sliceSpec h) cdBK_all) fbL2_ok
    rw [← gamT_eq] at h
    exact h
  · exact dCheckL_of hR hL dP1L_ok (slices_glL (Q := dML) (F := sliceL dML)
      (fun E h => sliceSpec h) dmK_all) dP3L_ok
  · exact fcCheckL_of hR hL hG rep_ok
      (slices_glL (Q := s0M glMask s0W) (F := sliceL (s0M glMask s0W)) (fun E h => sliceSpec h)
        s0K_all)
      (slices_glL (Q := s1M glMask s1W) (F := sliceL (s1M glMask s1W)) (fun E h => sliceSpec h)
        s1K_all)

end CertificateChecks.KernelM24L2
