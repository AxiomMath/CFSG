module

public import CFSG.Sporadic.Recognition.HSMultiplierInputs
import Certificates.Kernel.HSMult.TabK
import CFSG.Certificates.Kernel.TabMatSound

public section

namespace CertificateChecks.KernelHSMult

open CFSG.KC.VecK CFSG.KC.TabMat CertificateChecks.KernelVec.HS CFSG.Sporadic.HS.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.Sporadic.Bridge.TwoGen.Native

theorem tab : hsTabCheck = true := by
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
  have hai := (real_inv hP ha fun v hv => vmF_inv hAi hv).1
  have hbi := (real_inv hP hb fun v hv => vmF_inv hBi hv).1
  have h := relCheck_of_tabMatK hP ha hai hb hbi hsGenWords (by decide) hsPairs tabK
  rw [← hsCheckWords_eq] at h
  exact h

end CertificateChecks.KernelHSMult

end
