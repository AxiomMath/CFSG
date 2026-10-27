module

public import Certificates.Kernel.HMathieu.T12
public import CFSG.Certificates.Kernel.HMathieu.BfsSound
public import CFSG.Quasithin.H13.A5M12SylInputs

public section

namespace CertificateChecks.KernelHMathieu.T12

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12

theorem elems_eq : T12s2.elems = (E.map unpk).toArray := by
  have e : T12s2 = PT.ofGens 24 (gens.map unpk) 64 := by
    unfold T12s2
    congr 1
  rw [e]
  change bfsClosure 24 (gens.map unpk) 64 = _
  rw [bfsClosure_eq (List.all_eq_true.1 vpG), bfs]

theorem n_size : T12s2.n = T12s2.elems.size := rfl

end CertificateChecks.KernelHMathieu.T12

end
