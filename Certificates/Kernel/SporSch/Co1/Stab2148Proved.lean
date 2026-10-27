
module

public import Certificates.Kernel.SporSch.Co1.Stab2148

public section

namespace CertificateChecks.KernelSporSch.Co1Stab2148

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch.Co1Stab CertificateChecks.KernelSporSch.Co1Packed
open CertificateChecks.KernelSporSch.Co1Orbs

theorem e0_proved : enumOK (transposeRows 24 (unpack 24 24 PH0))
    (transposeRows 24 (unpack 24 24 PH1)) 16663704 1 (BF PH0 PH1 16663704 1) = true :=
  (vorbK_sound_proved O0.hr (by decide) (by decide) (by decide) O0.hc0 O0.hcN O0.hb O0.hp).1

theorem e1_proved : enumOK (transposeRows 24 (unpack 24 24 PH0))
    (transposeRows 24 (unpack 24 24 PH1)) 6009710 46575 (BF PH0 PH1 6009710 46575) = true :=
  (vorbK_sound_proved O1.hr (by decide) (by decide) (by decide) O1.hc0 O1.hcN O1.hb O1.hp).1

theorem e2_proved : enumOK (transposeRows 24 (unpack 24 24 PH0))
    (transposeRows 24 (unpack 24 24 PH1)) 769771 47104 (BF PH0 PH1 769771 47104) = true :=
  (vorbK_sound_proved O2.hr (by decide) (by decide) (by decide) O2.hc0 O2.hcN O2.hb O2.hp).1

theorem e3_proved : enumOK (transposeRows 24 (unpack 24 24 PH0))
    (transposeRows 24 (unpack 24 24 PH1)) 6244414 4600 (BF PH0 PH1 6244414 4600) = true :=
  (vorbK_sound_proved O3.hr (by decide) (by decide) (by decide) O3.hc0 O3.hcN O3.hb O3.hp).1

theorem q1_proved (n' : Nat) (hn : n' = 46575) (v : Nat) :
    ((List.range n').any fun i => (BF PH0 PH1 6009710 46575).pts[i]! == v) =
      memK O1.T O1.S 46575 v := by
  subst hn
  exact (vorbK_sound_proved O1.hr (by decide) (by decide) (by decide) O1.hc0 O1.hcN O1.hb
    O1.hp).2.2.2 v

theorem q2_proved (n' : Nat) (hn : n' = 47104) (v : Nat) :
    ((List.range n').any fun i => (BF PH0 PH1 769771 47104).pts[i]! == v) =
      memK O2.T O2.S 47104 v := by
  subst hn
  exact (vorbK_sound_proved O2.hr (by decide) (by decide) (by decide) O2.hc0 O2.hcN O2.hb
    O2.hp).2.2.2 v

theorem q3_proved (n' : Nat) (hn : n' = 4600) (v : Nat) :
    ((List.range n').any fun i => (BF PH0 PH1 6244414 4600).pts[i]! == v) =
      memK O3.T O3.S 4600 v := by
  subst hn
  exact (vorbK_sound_proved O3.hr (by decide) (by decide) (by decide) O3.hc0 O3.hcN O3.hb
    O3.hp).2.2.2 v

theorem qF_proved (v : Nat) :
    ((List.range 98280).any fun i => (BF PA PB 2 98280).pts[i]! == v) = memK F2.T F2.S 98280 v :=
  (vorbK_sound_proved F2.hr (by decide) (by decide) (by decide) F2.hc0 F2.hcN F2.hb F2.hp).2.2.2 v

theorem orb_proved : stabOrbCheck = true := by
  unfold stabOrbCheck
  rw [i0, i1, h0u, h1u, (invOKK_sound k0).1, (invOKK_sound k1).1, wf_unpack, wf_unpack]
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range]
  intro k hk
  rw [so]
  interval_cases k
  exacts [e0_proved, e1_proved, e2_proved, e3_proved]

theorem x_proved : stabXCheck = true := by
  unfold stabXCheck stabXCheckOf
  rw [full2]
  simp only [qF_proved, List.all_eq_true, List.mem_range]
  intro k hk
  interval_cases k
  exacts [x0, x1, x2, x3]

theorem mc0_proved : memCheckOf 0 (stabOrb (0 + 1)) = true := by
  unfold memCheckOf inEnum
  rw [so1]
  simp only [q1_proved (stabSize (0 + 1)) rfl]
  rw [m10]
  change (!false && !memK O1.T O1.S 46575 16663704 &&
    memK O1.T O1.S 46575 (16663704 ^^^ 6009710) == (0 == 2)) = true
  rw [m11, m12]
  rfl

theorem mc1_proved : memCheckOf 1 (stabOrb (1 + 1)) = true := by
  unfold memCheckOf inEnum
  rw [so2]
  simp only [q2_proved (stabSize (1 + 1)) rfl]
  rw [m20]
  change (!false && !memK O2.T O2.S 47104 16663704 &&
    memK O2.T O2.S 47104 (16663704 ^^^ 769771) == (1 == 2)) = true
  rw [m21, m22]
  rfl

theorem mc2_proved : memCheckOf 2 (stabOrb (2 + 1)) = true := by
  unfold memCheckOf inEnum
  rw [so3]
  simp only [q3_proved (stabSize (2 + 1)) rfl]
  rw [m30]
  change (!false && !memK O3.T O3.S 4600 16663704 &&
    memK O3.T O3.S 4600 (16663704 ^^^ 6244414) == (2 == 2)) = true
  rw [m31, m32]
  rfl

theorem mem_proved : memCheck = true := by
  unfold memCheck
  simp only [List.all_eq_true, List.mem_range]
  intro m hm
  interval_cases m
  exacts [mc0_proved, mc1_proved, mc2_proved]

end CertificateChecks.KernelSporSch.Co1Stab2148

end
