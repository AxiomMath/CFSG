module

public import CFSG.Certificates.Kernel.SortTreeChunks
public import Certificates.Kernel.MonsterB.Orb3132K0
public import Certificates.Kernel.MonsterB.Orb3132K39a
public import Certificates.Kernel.MonsterB.Orb3132K39b
public import Certificates.Kernel.MonsterB.Orb3132K35a
public import Certificates.Kernel.MonsterB.Orb3132K35b
public import Certificates.Kernel.MonsterB.Orb3132K35c
public import Certificates.Kernel.MonsterB.Orb3132K35d
public import Certificates.Kernel.MonsterB.Orb3132K35e

public section

namespace CertificateChecks.Orb3132

open CFSG.KLie.CT CFSG.KC.SortTree

theorem slice_add {r : ℕ} {rec : ℕ → ℕ} {n wl wp a m b : ℕ}
    (ha : ∀ c < a, chunkOK act 17 (fun _ => true) r rec n 22 wl wp 2048 c = true)
    (h : slice r rec n wl wp a m = true) (hb : a + m = b) :
    ∀ c < b, chunkOK act 17 (fun _ => true) r rec n 22 wl wp 2048 c = true := by
  subst hb
  exact forall_lt_add ha ((allN_iff _ _).1 h)

theorem none_lt {P : ℕ → Prop} : ∀ c < 0, P c := fun c hc => absurd hc (Nat.not_lt_zero c)

theorem tree60 : treeOK act 17 (fun _ => true) 60 rec60 1408 22 3 11 2048 1 = true :=
  treeOK_of_chunks (by decide) (slice_add none_lt s60 rfl)

theorem tree32 : treeOK act 17 (fun _ => true) 32 rec32 20736 22 4 15 2048 11 = true :=
  treeOK_of_chunks (by decide) (slice_add none_lt s32 rfl)

theorem tree39 : treeOK act 17 (fun _ => true) 39 rec39 228096 22 4 18 2048 112 = true :=
  treeOK_of_chunks (by decide) (slice_add (slice_add (slice_add (slice_add none_lt
    s39_0 rfl) s39_1 rfl) s39_2 rfl) s39_3 rfl)

theorem tree35 : treeOK act 17 (fun _ => true) 35 rec35 798336 22 4 20 2048 390 = true :=
  treeOK_of_chunks (by decide) (slice_add (slice_add (slice_add (slice_add (slice_add
    (slice_add (slice_add (slice_add (slice_add (slice_add (slice_add (slice_add (slice_add
      none_lt s35_0 rfl) s35_1 rfl) s35_2 rfl) s35_3 rfl) s35_4 rfl) s35_5 rfl) s35_6 rfl)
      s35_7 rfl) s35_8 rfl) s35_9 rfl) s35_10 rfl) s35_11 rfl) s35_12 rfl)

end CertificateChecks.Orb3132

end
