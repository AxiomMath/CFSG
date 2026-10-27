module

public import Certificates.Kernel.FixBoundK.TrivK
public import Certificates.Kernel.FixBoundK.TrivAutK
public import CFSG.Certificates.Kernel.FixBoundK.TrivSound

public section

namespace CertificateChecks.KernelFixBoundK.TrivGlue

open CFSG.KC.FixBoundK CFSG.KC.FixBoundK.Triv CFSG.KC.FixBoundK.TrivSound
  CertificateChecks.KernelFixBoundK.TrivD

theorem hrep : ∀ i < reps.length, trivAt reps k1s i = true := by
  intro i hi
  rw [← lenS_eq, TrivAutK.repLen] at hi
  interval_cases i
  · exact TrivK.rep0
  · exact TrivK.rep1

theorem hws : ∀ c < 16,
    wsAt CertificateChecks.Perm3018.GS CertificateChecks.Perm3018.GA reps ws c = true := by
  intro c hc
  interval_cases c
  exacts [TrivK.ws0, TrivK.ws1, TrivK.ws2, TrivK.ws3, TrivK.ws4, TrivK.ws5, TrivK.ws6,
    TrivK.ws7, TrivK.ws8, TrivK.ws9, TrivK.ws10, TrivK.ws11, TrivK.ws12, TrivK.ws13, TrivK.ws14,
    TrivK.ws15]

theorem cw_eq {x : Nat} (hx : IsCw x) : ∃ m < 4096, cwK m = x := exists_cwK TrivAutK.code hx

theorem triv_case {x₁ : Nat} (hx₁ : IsCw x₁) :
    x₁ = 0 ∨ x₁ = omK ∨
      (∀ x₂, IsCw x₂ → synK (x₁ &&& x₂) = 0 →
        x₂ = 0 ∨ x₂ = omK ∨ x₂ = x₁ ∨ x₂ = x₁ ^^^ omK ∨
          (∀ x₃, IsCw x₃ → synK (x₁ &&& x₃) = 0 → synK (x₂ &&& x₃) = 0 →
            x₃ = 0 ∨ x₃ = omK ∨ x₃ = x₁ ∨ x₃ = x₁ ^^^ omK ∨ x₃ = x₂ ∨ x₃ = x₂ ^^^ omK ∨
              x₃ = x₁ ^^^ x₂ ∨ x₃ = x₁ ^^^ x₂ ^^^ omK)) :=
  triv_spec TrivAutK.code TrivAutK.aut hrep hws hx₁

end CertificateChecks.KernelFixBoundK.TrivGlue

end
