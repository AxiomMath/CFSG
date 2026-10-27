module

public import Certificates.Kernel.L52Insp443.Checks
public import Certificates.Kernel.L52Insp443.TabChk
public import CFSG.Certificates.Kernel.L52Insp443.Cent

public section

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem centZ_of {z : ℕ} (hz : ch725109z z = true) (ht : ch725109t z = true)
    (hl : (e16.getD z []).length = 4) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    centTestS 31 (e16.getD z []) (spanTabs 31 (e16.getD z [])) T = false := by
  obtain ⟨h1, h2⟩ := and2 hz
  obtain ⟨h2, h3⟩ := and2 h2
  obtain ⟨h3, h4⟩ := and2 h3
  have ht' : tabsK (D.zB.getD z []) (e16.getD z []) = true := ht
  refine centTestS_false_of ht' ht' h1 h2 h3 ?_ h hT
  rw [Nat.eq_of_beq_eq_true h4, length_of_tabsK ht', hl]
  rfl

theorem e16_centTest {z : ℕ} (hz : z < 7) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    centTestS 31 (e16.getD z []) (spanTabs 31 (e16.getD z [])) T = false := by
  interval_cases z
  · exact centZ_of ch725109z0 ch725109t0 rfl h hT
  · exact centZ_of ch725109z1 ch725109t1 rfl h hT
  · exact centZ_of ch725109z2 ch725109t2 rfl h hT
  · exact centZ_of ch725109z3 ch725109t3 rfl h hT
  · exact centZ_of ch725109z4 ch725109t4 rfl h hT
  · exact centZ_of ch725109z5 ch725109t5 rfl h hT
  · exact centZ_of ch725109z6 ch725109t6 rfl h hT

theorem tabs_wB {w : ℕ} (hu : ch725109u w = true) :
    tabsK (List.append (D.a0B.getD w []) (D.a1B.getD w [])) (wB w) = true := by
  obtain ⟨h1, h2⟩ := and2 hu
  unfold wB
  exact tabsK_append h2 h1

theorem centW_of {k w : ℕ} (hc : ch725109c k = true) (hr : ch725109r k = true)
    (hw : ch725109w w = true) (hu : ch725109u w = true) (hkw : D.k2w.getD k 0 = w)
    (hl : (wB w).length = 6) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    centTestS 31 (cands7.getD (k + 12) []) (spanTabs 31 (wB w)) T = false := by
  obtain ⟨c1, c2⟩ := and2 hc
  obtain ⟨w1, w2⟩ := and2 hw
  obtain ⟨w2, -⟩ := and2 w2
  rw [hkw] at c1
  have hr' : tabsK (D.k2B.getD k []) (cands7.getD (k + 12) []) = true := hr
  have hW := tabs_wB hu
  refine centTestS_false_of hr' hW w1 w2 c1 ?_ h hT
  rw [Nat.eq_of_beq_eq_true c2, length_of_tabsK hW, hl]
  rfl

theorem k2_centTest {k : ℕ} (hk : k < 12) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    centTestS 31 (cands7.getD (k + 12) []) (spanTabs 31 (wB (k / 6))) T = false := by
  interval_cases k
  · exact centW_of ch725109c0 ch725109r0 ch725109w0 ch725109u0 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c1 ch725109r1 ch725109w0 ch725109u0 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c2 ch725109r2 ch725109w0 ch725109u0 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c3 ch725109r3 ch725109w0 ch725109u0 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c4 ch725109r4 ch725109w0 ch725109u0 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c5 ch725109r5 ch725109w0 ch725109u0 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c6 ch725109r6 ch725109w1 ch725109u1 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c7 ch725109r7 ch725109w1 ch725109u1 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c8 ch725109r8 ch725109w1 ch725109u1 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c9 ch725109r9 ch725109w1 ch725109u1 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c10 ch725109r10 ch725109w1 ch725109u1 (by decide +kernel) rfl h hT
  · exact centW_of ch725109c11 ch725109r11 ch725109w1 ch725109u1 (by decide +kernel) rfl h hT

theorem c2_of {k : ℕ} (hk : ch725109k k = true) (hq : ch725109q k = true) (h : G) {T : Table}
    (hT : Rep 31 T (glPerm h)) : c2TestS 31 (cands7.getD (k1idx k) []) 128 T = false := by
  obtain ⟨-, k2⟩ := and2 hk
  obtain ⟨-, k3⟩ := and2 k2
  obtain ⟨k3, -⟩ := and2 k3
  exact c2TestS_false hq (Nat.eq_of_beq_eq_true k3) h hT

theorem k1_c2Test {k : ℕ} (hk : k < 6) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    c2TestS 31 (cands7.getD (k1idx k) []) 128 T = false := by
  interval_cases k
  · exact c2_of ch725109k0 ch725109q0 h hT
  · exact c2_of ch725109k1 ch725109q1 h hT
  · exact c2_of ch725109k2 ch725109q2 h hT
  · exact c2_of ch725109k3 ch725109q3 h hT
  · exact c2_of ch725109k4 ch725109q4 h hT
  · exact c2_of ch725109k5 ch725109q5 h hT

end CertificateChecks.KernelL52I

end
