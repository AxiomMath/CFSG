module

public import Certificates.Data.FzJtCheck
import CFSG.Certificates.Kernel.FzJt.Sound
import Certificates.Kernel.FzJt.Checks

public section

namespace CertificateChecks.KernelFzJt

open Certificates.FzJ36 Certificates.FzFus Certificates.FzJt Certificates.FzJt.K

theorem f2Fact : F2Fact := by
  intro q hq
  rcases hq with rfl | rfl | rfl
  · exact f2B_sound ch441783f2_64 _ (by decide +kernel)
  · exact f2B_sound ch441783f2_256 _ (by decide +kernel)
  · exact f2B_sound ch441783f2_338 _ (by decide +kernel)

theorem f3Fact : F3Fact := by
  intro q hq
  have hm := sixQ_mem q hq
  simp only [sixQ, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact f3B_sound ch441783f3_64 _ (by decide +kernel)
  · exact f3B_sound ch441783f3_82 _ (by decide +kernel)
  · exact f3B_sound ch441783f3_256 _ (by decide +kernel)
  · exact f3B_sound ch441783f3_320 _ (by decide +kernel)
  · exact f3B_sound ch441783f3_274 _ (by decide +kernel)
  · exact f3B_sound ch441783f3_338 _ (by decide +kernel)

theorem f4Fact : F4Fact := f4B_sound ch441783f4

end CertificateChecks.KernelFzJt
