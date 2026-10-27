module

public import CFSG.Certificates.Kernel.Misc.Sp6NSound

public section

namespace CFSG.KC.Sp6N

open CFSG.KGroups.Sp6

theorem sp6n_normB : normB = true := by decide +kernel

theorem cert4157_count_norm : countCheck 64 1451520 = true ∧ normCheck 64 s0 n0List = true :=
  ⟨countCheck_ok, normCheck_of sp6n_normB⟩

end CFSG.KC.Sp6N

end
