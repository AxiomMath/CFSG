module

public import Certificates.Kernel.Y2LHS.Checks
public import Certificates.Kernel.HSMult.TabK
public import CFSG.Certificates.Kernel.TabMatSound

public section

namespace CertificateChecks.KernelY2LHS

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.VecK CFSG.KC.TabMat CertificateChecks.KernelVec.HS
  CFSG.Sporadic.HS.Native CFSG.OddStandard.HigherRank.G2Three.Sec2
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.Sporadic.Th.Native CertificateChecks.KernelHSMult CFSG.CosetTable

theorem real_ab : VPts (hsData ()).d (hsData ()).n (lk Pt 32) ∧
    Realizes (hsData ()).d (hsData ()).n (lk Pt 32) ((hsData ()).orbit ()).alpha NA ∧
    Realizes (hsData ()).d (hsData ()).n (lk Pt 32)
      (invT (hsData ()).n ((hsData ()).orbit ()).alpha) NAi ∧
    Realizes (hsData ()).d (hsData ()).n (lk Pt 32) ((hsData ()).orbit ()).beta NB ∧
    Realizes (hsData ()).d (hsData ()).n (lk Pt 32)
      (invT (hsData ()).n ((hsData ()).orbit ()).beta) NBi := by
  have horb : ∀ h < (hsData ()).n, orbAt (hsData ()).d (hsData ()).n NA NB Pt AT BT h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact orb_0
      | 1, _ => exact orb_1
      | 2, _ => exact orb_2
      | 3, _ => exact orb_3
      | 4, _ => exact orb_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hbfs : ∀ h < (hsData ()).n, bfsAt (hsData ()).n AT BT FO h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact bfs_0
      | 1, _ => exact bfs_1
      | 2, _ => exact bfs_2
      | 3, _ => exact bfs_3
      | 4, _ => exact bfs_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hsort : ∀ h < (hsData ()).n, sortAt (hsData ()).n Pt S IP SP h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact sort_0
      | 1, _ => exact sort_1
      | 2, _ => exact sort_2
      | 3, _ => exact sort_3
      | 4, _ => exact sort_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hP := vpts_of hn horb hsort
  obtain ⟨ha, hb⟩ := orbit_real (hsData ()) hA hB hseed hn hP0 horb hbfs hsort
  exact ⟨hP, ha, (real_inv hP ha fun v hv => vmF_inv hAi hv).1, hb,
    (real_inv hP hb fun v hv => vmF_inv hBi hv).1⟩

theorem rels_eq : (y2l_ws26 2 false).map (y2l_subst (y2l_hsW ())) =
    (y2lPairs.map fun q => substWord y2lGws q.1 ++ q.2).map natWord := by
  rw [words_eq]
  simp [y2lPairs, y2l_subst_eq]

theorem check : y2l_hsCheck () = true := by
  obtain ⟨hP, ha, hai, hb, hbi⟩ := real_ab
  have hn : (hsData ()).n = 1100 := by decide +kernel
  unfold y2l_hsCheck
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [rels_eq]
    exact relCheck_of_tabMatK hP ha hai hb hbi y2lGws (by decide +kernel) y2lPairs tabK
  · rw [List.all_eq_true]
    intro v hv
    have h7 := List.all_eq_true.1 sevenK v hv
    obtain ⟨x, hx, hne⟩ := List.any_eq_true.1 h7
    have hx' : x < (hsData ()).n := by rw [hn]; exact List.mem_range.1 hx
    have hR := (real_wordTab hP ha hai hb hbi v).2 x hx'
    refine List.any_eq_true.2 ⟨x, List.mem_range.2 hx', ?_⟩
    rw [bne_iff_ne]
    intro e
    rw [e] at hR
    rw [← hR.2, Nat.beq_refl] at hne
    exact absurd hne (by decide)

end CertificateChecks.KernelY2LHS

end
