module

import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.ForallTreeFrom
import Mathlib.Tactic.IntervalCases
import Certificates.Kernel.Sporadic.Fi24Seven.NegI
public import Certificates.Kernel.Sporadic.Fi24Seven.GlueK
import Certificates.Kernel.Sporadic.Fi24Seven.C00
import Certificates.Kernel.Sporadic.Fi24Seven.C01
import Certificates.Kernel.Sporadic.Fi24Seven.C02
import Certificates.Kernel.Sporadic.Fi24Seven.C03
import Certificates.Kernel.Sporadic.Fi24Seven.C04
import Certificates.Kernel.Sporadic.Fi24Seven.C05
import Certificates.Kernel.Sporadic.Fi24Seven.C06
import Certificates.Kernel.Sporadic.Fi24Seven.C07A
import Certificates.Kernel.Sporadic.Fi24Seven.C07B
import Certificates.Kernel.Sporadic.Fi24Seven.C08
import Certificates.Kernel.Sporadic.Fi24Seven.C09
import Certificates.Kernel.Sporadic.Fi24Seven.C10
import Certificates.Kernel.Sporadic.Fi24Seven.C11
import Certificates.Kernel.Sporadic.Fi24Seven.C12
import Certificates.Kernel.Sporadic.Fi24Seven.C13
import Certificates.Kernel.Sporadic.Fi24Seven.C14
import Certificates.Kernel.Sporadic.Fi24Seven.C15
import Certificates.Kernel.Sporadic.Fi24Seven.C16
import Certificates.Kernel.Sporadic.Fi24Seven.C17
import Certificates.Kernel.Sporadic.Fi24Seven.C18
import Certificates.Kernel.Sporadic.Fi24Seven.C19
import Certificates.Kernel.Sporadic.Fi24Seven.C20
import Certificates.Kernel.Sporadic.Fi24Seven.C21

public section

namespace CertificateChecks.KernelF24S

open CFSG.KD.F24S

#kc_forall_tree chunksA_ok (fun k => CFSG.KD.F24S.CK k = true) 107 CFSG.KD.F24S.ck

#kc_forall_tree_from chunksC_ok (fun k => CFSG.KD.F24S.CK k = true) 123 220 CFSG.KD.F24S.ck

theorem chunks_ok : ChunksOK := by
  refine ⟨gi_ok, fun k hk => ?_⟩
  have hk' : k < 343 := hk
  by_cases h1 : k < 107
  · exact Or.inl (chunksA_ok k h1)
  by_cases h2 : 123 ≤ k
  · have h : CK (123 + (k - 123)) = true := chunksC_ok (k - 123) (by change k - 123 < 220; omega)
    rw [Nat.add_sub_cancel' h2] at h
    exact Or.inl h
  have a : 107 ≤ k := by omega
  have b : k < 123 := by omega
  interval_cases k
  exacts [Or.inl ck107, Or.inr cki108, Or.inl ck109, Or.inr cki110, Or.inl ck111, Or.inr cki112,
    Or.inl ck113, Or.inr cki114, Or.inl ck115, Or.inr cki116, Or.inl ck117, Or.inr cki118,
    Or.inl ck119, Or.inr cki120, Or.inl ck121, Or.inr cki122]

theorem fi24kOK_true : CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.fi24kOK () = true :=
  fi24kOK_of chunks_ok

end CertificateChecks.KernelF24S

end
