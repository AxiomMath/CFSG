
module

public import Certificates.Kernel.MonsterB.Orb14Checks
import all CFSG.Fischer.F4
public import CFSG.Certificates.Kernel.MonsterB.Orb14Sound

@[expose] public section

namespace CertificateChecks.Orb14

open CFSG.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census
open CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT CFSG.KC.Bfs CertificateChecks.Tau1408

theorem sing_spec : b6SingArr.size = 693 ∧ ∀ j < 693, b6SingArr[j]! < 4096 ∧
    fget SGL j 12 = b6SingArr[j]! :=
  bindL_spec (by decide) (andB_eq_true.1 kSing).1

theorem sing_inc : (∀ t < 693, fget SGL t 12 < 4096) ∧
    ∀ a < 693, ∀ b < 693, a < b → fget SGL a 12 < fget SGL b 12 :=
  incOK_spec (andB_eq_true.1 (andB_eq_true.1 kSing).2).1

theorem sing_pos : 0 < fget SGL 0 12 := by
  have := (andB_eq_true.1 (andB_eq_true.1 kSing).2).2
  rwa [Nat.blt_eq] at this


theorem sing_get {j : ℕ} (hj : j < 693) : b6SingArr[j]! = fget SGL j 12 :=
  ((sing_spec.2 j hj).2).symm


theorem sing_nz {q : ℕ} (hq : q < 693) : b6SingArr[q]! ≠ 0 := by
  rw [sing_get hq]
  rcases Nat.eq_zero_or_pos q with rfl | h
  · exact Nat.pos_iff_ne_zero.1 sing_pos
  · exact Nat.pos_iff_ne_zero.1 (lt_trans sing_pos (sing_inc.2 0 (by decide) q hq h))

theorem sing_nodup : b6SingArr.toList.Nodup := by
  have h := nodup_map_of_inj (xs := b6SingArr) id (fun a ha b hb e => by
    rw [sing_spec.1] at ha hb
    change b6SingArr[a]! = b6SingArr[b]! at e
    rw [sing_get ha, sing_get hb] at e
    rcases lt_trichotomy a b with h | h | h
    · exact absurd e (ne_of_lt (sing_inc.2 a ha b hb h))
    · exact h
    · exact absurd e (ne_of_gt (sing_inc.2 b hb a ha h)))
  rwa [List.map_id] at h

end CertificateChecks.Orb14

end
