module

public import Certificates.Kernel.HMathieu.T22
public import CFSG.Certificates.Kernel.HMathieu.BfsSound
public import CFSG.Quasithin.Background.HMathieuSyl22Inputs

public section

namespace CertificateChecks.KernelHMathieu.T22

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.Quasithin.H.Mathieu

theorem elems_eq : T22s2.elems = (E.map unpk).toArray := by
  have e : T22s2 = PT.ofGens 24 (gens.map unpk) 64 := by
    unfold T22s2 gens22s2
    congr 1
  rw [e]
  change bfsClosure 24 (gens.map unpk) 64 = _
  rw [bfsClosure_eq (List.all_eq_true.1 vpG), bfs]

theorem n_size : T22s2.n = T22s2.elems.size := rfl

end CertificateChecks.KernelHMathieu.T22

end
