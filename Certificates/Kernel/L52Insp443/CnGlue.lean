module

public import Certificates.Kernel.L52Insp443.CentGlue
public import Certificates.Kernel.L52Insp443.MChk
public import CFSG.Certificates.Kernel.L52Insp443.CentN

public section

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem cnOf {w : ℕ} (hm : ch725109m w = true) (hw : ch725109w w = true)
    (hu : ch725109u w = true) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    cnTestS 31 (e64a0.getD w []) (e64a1.getD w []) (spanTabs 31 (e64a1.getD w []))
      (spanTabs 31 (wB w)) T = false := by
  obtain ⟨m1, m2⟩ := and2 hm
  obtain ⟨m2, m3⟩ := and2 m2
  obtain ⟨m3, m4⟩ := and2 m3
  obtain ⟨m4, m5⟩ := and2 m4
  obtain ⟨w1, r⟩ := and2 hw
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨w4, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨w8, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨-, w11⟩ := and2 r
  obtain ⟨u0, u1⟩ := and2 hu
  rw [listBeq_iff] at w1 w4
  have w8' := (listBeq_iff _ _).mp ((allK_iff _ _).mp w8 1 (List.mem_range.mpr (by norm_num)))
  rw [w4] at w8'
  rw [← w1, mapMulK_eq] at m2 m3 m4
  rw [← w1] at m5
  obtain ⟨-, t2⟩ := and2 w11
  obtain ⟨-, t3⟩ := and2 t2
  refine cnTestS_false (wc := List.append (D.a0B.getD w []) (D.a1B.getD w [])) (τ := D.tau.getD w 0)
    u0 u1 (tabs_wB hu) m1 ((nodupK_iff _).mp m2) (fun c hc => ?_) ?_ (fun s hs b hb => ?_) ?_ h hT
  · obtain ⟨c1, c2⟩ := and2 ((allK_iff _ _).mp m4 c hc)
    exact ⟨c1, fun b hb => (commK_iff c b).mp ((allK_iff _ _).mp c2 b hb)⟩
  · obtain ⟨-, r⟩ := and2 hw
    obtain ⟨-, r⟩ := and2 r
    obtain ⟨-, r⟩ := and2 r
    obtain ⟨-, r⟩ := and2 r
    obtain ⟨-, r⟩ := and2 r
    obtain ⟨-, r⟩ := and2 r
    obtain ⟨-, r⟩ := and2 r
    obtain ⟨-, r⟩ := and2 r
    obtain ⟨-, r⟩ := and2 r
    obtain ⟨r, -⟩ := and2 r
    exact (Nat.eq_of_beq_eq_true r).trans (Nat.eq_of_beq_eq_true m3).symm
  · exact (commK_iff s b).mp ((allK_iff _ _).mp ((allK_iff _ _).mp m5 s hs) b hb)
  · obtain ⟨a, ha, hall⟩ := (anyK_iff _ _).mp t3
    refine ⟨a, ha, fun a' ha' e => ?_⟩
    rw [w8'] at ha'
    have := notB_true.mp ((allK_iff _ _).mp hall a' ha')
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)

theorem e64_cnTest {w : ℕ} (hw : w < 2) (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    cnTestS 31 (e64a0.getD w []) (e64a1.getD w []) (spanTabs 31 (e64a1.getD w []))
      (spanTabs 31 (wB w)) T = false := by
  interval_cases w
  · exact cnOf ch725109m0 ch725109w0 ch725109u0 h hT
  · exact cnOf ch725109m1 ch725109w1 ch725109u1 h hT

end CertificateChecks.KernelL52I

end
