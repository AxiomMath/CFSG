module

public import Certificates.Kernel.Fi22Core.Chain
public import Certificates.Kernel.Fi22Core.Sep

public section

namespace CertificateChecks.KernelFi22C

open CFSG.KS CFSG.KS.Fi22L CFSG.KS.TW CFSG.KS.TBfs CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native
  CFSG.Perm.Native CFSG.F3.Native

theorem action_ok (hcard : Hcard) : actionChecks orbL 3 = true := by
  unfold actionChecks
  dsimp only
  rw [t2_eq.1]
  simp only [Bool.and_eq_true]
  have gen := CertificateChecks.KernelFi22.Letters.gen_ok
  have hidx : sepIdx.all (· < 3510) = true := by
    rw [← Array.all_toList]
    decide
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, sep_ok⟩, hidx⟩, (chain_eq hcard).2 3⟩, sizes hcard⟩,
    t2_eq.2⟩, ?_⟩, cover hcard⟩
  · rw [keys_size]
    rfl
  · have e : orbL.alpha = orbTab 0 := rfl
    rw [e, orbTab_size]
    rfl
  · have e : orbL.beta = orbTab 1 := rfl
    rw [e, orbTab_size]
    rfl
  · unfold invoOK
    rw [TW.allIn_iff]
    intro i hi
    rw [(alpha_get hi).1, (alpha_get (alpha_get hi).2).1, (tree_facts hi).2.2.1, beq_self_eq_true]
  · exact invOK_of (tr_beta gen) (tr_binv gen) fun i hi => (gen_facts gen hi).2.2.2.1
  · have c := cnts.2.2.2.2.2
    simp only [tbfsRec, Array.size_ofFn, c]
    rfl

theorem fi22_cert_of (hcard : Hcard) :
    (matrixChecks () && conjOrbitOK 77 (matA ()) (matA ()) (matB ()) (matBi ()) orbL 3 &&
      actionChecks orbL 3 && productChecks orbL) = true := by
  rw [matrix_ok, conj_ok, action_ok hcard, product_ok]
  rfl

end CertificateChecks.KernelFi22C

end
