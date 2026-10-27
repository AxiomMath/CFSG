module

public import Certificates.Kernel.J4Loc.StabChk
public import CFSG.Certificates.Kernel.J4Loc.StabSound

public section

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Loc CFSG.KD.J4Loc CFSG.KS.J4Loc CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

theorem k4178_basis :
    ∀ a ∈ V0F, ∀ b ∈ V0F, ∀ c ∈ V0F, a ≠ 0 → b ≠ 0 → b ≠ a → c ≠ 0 → c ≠ a → c ≠ b →
      c ≠ a ^^^ b → ∃ w : List ℤ, (∀ ℓ ∈ w, ℓ ∈ letters) ∧
        w.foldr act 422 = a ∧ w.foldr act 553 = b ∧ w.foldr act 1131 = c :=
  stab_word (fun l hl => by interval_cases l <;> rfl) ch4178_ok ch4178_cov

end CertificateChecks.KernelJ4Loc

end
