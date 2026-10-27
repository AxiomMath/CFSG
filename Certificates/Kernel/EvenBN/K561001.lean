module

public import Certificates.Data.KappaDN
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelEvenBN.K561001

open Certificates.KappaD

@[expose] def clChunk (k : ℕ) : Bool :=
  (((slList ()).drop (24 * k)).take 24).all fun a =>
    (List.finRange 4).all fun j => decide (rowsOf (a * tMat j) ∈ slRows ())

@[expose] def wChunk (e₁ e₂ : ZMod 2) : Bool :=
  decide (∀ e₃ d₁ : ZMod 2,
    wordOKb (slRows ()) tMat (wordOf e₁ e₂ e₃ d₁) e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1 = true)

theorem oneK : decide (rowsOf 1 ∈ slRows ()) = true := by quickRfl

theorem clK0 : clChunk 0 = true := by quickRfl
theorem clK1 : clChunk 1 = true := by quickRfl
theorem clK2 : clChunk 2 = true := by quickRfl
theorem clK3 : clChunk 3 = true := by quickRfl
theorem clK4 : clChunk 4 = true := by quickRfl
theorem clK5 : clChunk 5 = true := by quickRfl
theorem clK6 : clChunk 6 = true := by quickRfl
theorem clK7 : clChunk 7 = true := by quickRfl

theorem wK00 : wChunk 0 0 = true := by quickRfl
theorem wK01 : wChunk 0 1 = true := by quickRfl
theorem wK10 : wChunk 1 0 = true := by quickRfl
theorem wK11 : wChunk 1 1 = true := by quickRfl

end CertificateChecks.KernelEvenBN.K561001

end
