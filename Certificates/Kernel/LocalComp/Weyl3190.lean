module

public import Certificates.Kernel.LocalComp.Weyl3187
public import CFSG.Certificates.Kernel.LocalCompAglSound
public import CFSG.Certificates.Kernel.LocalCompFrameSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAGLData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3190

open CFSG.KC.Enum CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CertificateChecks.KernelLC

theorem kG : ∀ i : Fin 8, pg 3 7 12369168 i = frameSinger i := by decide

theorem kH : ∀ i : Fin 8, pg 3 7 16434369 i = frameFlip i := by decide

theorem kAgl : aglK 12369168 16434369 = true := by quickRfl

theorem k16 : f16K E8.RT E8.FT E8.NEG W3220.KP = true := by quickRfl

theorem plane_aff : ∀ a b d e : Fin 8, a ≠ b → a ≠ d → b ≠ d →
    (planeThrough a b d).testBit e = false →
      e ≠ a ∧ e ≠ b ∧ e ≠ d ∧ (e : ℕ) ≠ a ^^^ (b ^^^ d) := by
  decide +kernel

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem cert3190 : (∀ a b d e : Fin 8, a ≠ b → a ≠ d → b ≠ d → (planeThrough a b d).testBit e = false →
      ∃ τ ∈ Subgroup.closure frameGens, τ 0 = a ∧ τ 1 = b ∧ τ 2 = d ∧ τ 4 = e)
    ∧ (frame16Check = true) := by
  refine ⟨fun a b d e hab had hbd hp => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := plane_aff a b d e hab had hbd hp
    exact agl_sound kG kH kAgl hab had hbd h1 h2 h3 h4
  · rw [frame16Check_eq]
    exact frame16_sound E8.bind E8.sorted E8.hrt E8.neg E8.froots E8.ft0 E8.hft W3220.kKP
      W3187.kHF k16

end CertificateChecks.KernelLC.W3190

end
