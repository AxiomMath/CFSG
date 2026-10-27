module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0GenData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0GenData
public import Certificates.Kernel.J4M2.SlpB
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Gam

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E CFSG.Sporadic.J4Schreier
  CertificateChecks.KernelSporSch.J4E7 CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.KC.J4Slp
  CFSG.Sporadic.GLQ

theorem c12611_regs : RegsOK 170 l0Regs l0R :=
  runK_ok CertificateChecks.KernelSporSch.J4Real.hK (slpB_init_ok (by norm_num)) l0Prog c12611lt

theorem c12611_pair {r : Nat} (hr : r < 170) : PairOK (l0P r) (regM l0R r) (regI l0R r) :=
  c12611_regs.2.2 r hr

theorem c12611_elt {r p : Nat} (hr : r < 170) (h : eltK l0R r p = true) : l0Elt r p = true := by
  have hP := c12611_pair hr
  have hw := hP.1.1
  have wZ := wfN_of rows.1
  have wI := (CFSG.KS.SporSch.J4B.id_enc CertificateChecks.KernelSporSch.J4Real.hK).1
  unfold eltK at h
  rw [CFSG.KC.J4Slp.strictB_eq] at h
  obtain ⟨h1, h234⟩ := andB_parts h
  obtain ⟨h2, h34⟩ := andB_parts h234
  obtain ⟨h3, h4⟩ := andB_parts h34
  rw [← hP.1.2] at h1 h2 h3 h4
  unfold l0Elt
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨eq_sound CertificateChecks.KernelSporSch.J4Real.hK hw wZ wZ hw h1,
    eq_sound CertificateChecks.KernelSporSch.J4Real.hK hw wfN_cE wfN_cE hw h2⟩,
    pow_one_sound CertificateChecks.KernelSporSch.J4Real.hK hw h3⟩, ?_⟩
  change neOK (l0P r).1 (CFSG.Sporadic.SmallF2.Native.idRows 112) = true
  rw [slpB_neOK hw wI, (CFSG.KS.SporSch.J4B.id_enc CertificateChecks.KernelSporSch.J4Real.hK).2]
  exact h4

theorem c12611_prod {r s e : Nat} (hr : r < 170) (hs : s < 170)
    (h : Nat.beq (powJ c rm one (mulJ c rm (regM l0R r) (regM l0R s)) e) Z0 = true) :
    O.eq (O.pow (mulP (l0P r) (l0P s)).1 e) gamZ0 = true := by
  have hP := mulP_ok CertificateChecks.KernelSporSch.J4Real.hK (c12611_pair hr) (c12611_pair hs)
  exact slpB_pow_eq hP.1.1 (wfN_of rows.1) (by rw [hP.1.2]; exact h)

theorem l0OK_ok : l0OK = true := by
  have hc := c12611run
  rw [slpB_forceB_eq] at hc
  unfold l0K at hc
  obtain ⟨e0, hc⟩ := andB_parts hc
  obtain ⟨e1, hc⟩ := andB_parts hc
  obtain ⟨e2, hc⟩ := andB_parts hc
  obtain ⟨e3, hc⟩ := andB_parts hc
  obtain ⟨q7, q11⟩ := andB_parts hc
  have wZ := wfN_of rows.1
  unfold l0OK
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨c12611lt, cEOK_ok⟩, gamZ0OK_ok⟩,
    eq_one_sound CertificateChecks.KernelSporSch.J4Real.hK wZ wZ zz_chk⟩,
    c12611_elt (by norm_num) e0⟩, c12611_elt (by norm_num) e1⟩, c12611_elt (by norm_num) e2⟩,
    c12611_elt (by norm_num) e3⟩, c12611_prod (by norm_num) (by norm_num) q7⟩,
    c12611_prod (by norm_num) (by norm_num) q11⟩

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction in
theorem c12611 : l0OK = true := l0OK_ok

end CertificateChecks.KernelJ4Gam

end
