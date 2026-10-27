module

public import Certificates.Kernel.LocalComp.L34Para.Data
public import Certificates.Kernel.L34Tw.Data
public import Certificates.Data.Kernel.L34Tw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Tw

open CFSG.KC.L34Tw CertificateChecks.KernelLC.L34TwD

@[expose] noncomputable def r₄K : Nat := mulK (L34R.G 4) (L34R.G 5)

theorem ch33101_norm : normK L34PT.T L34PT.G (L34R.G 4) (L34R.G 5) = true := by quickRfl

theorem ch33201_klein : kleinAllK L34PT.T (L34R.G 4) (L34R.G 5) W = true := by quickRfl

theorem ch33209_t : tK L34PT.T (L34R.G 4) (L34R.G 5) (D 0) = true := by quickRfl

theorem ch33211_idx : D 1 < 64 ∧ D 2 < 64 := by decide

theorem ch33211_cent : centK L34PT.G (L34R.G 4) (L34R.G 5) (L34PT.T (D 1)) = true := by quickRfl

theorem ch33211_inv : inv2K (mulK (L34PT.T (D 2)) r₄K) = true := by quickRfl

theorem ch33211_uni : uniK L34PT.T r₄K U = true := by quickRfl

theorem ch33211_big : bigK L34PT.T 16 = true := by quickRfl

theorem ch33211_q : qAllK L34PT.T r₄K Q I = true := by quickRfl

theorem ch33211_p : pAllK L34PT.T r₄K Q I = true := by quickRfl

end CertificateChecks.KernelLC.L34Tw

end
