module

public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import Certificates.Data.Kernel.LocalQT.Tc
public import Certificates.Data.W4Fi22OuterGen
meta import Certificates.Data.W4Fi22OuterGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KD.LQT.C1037301

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.LQT.TC
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row CertificateChecks.KernelSpor

theorem hT : tcK 3510 12 [Fi22W.G 0, Fi22W.G 1] [Fi22W.GI 0, Fi22W.GI 1] (Fi22ExtT.L 25)
    (Fi22ExtT.L 25) fi22GenWC fi22GenProg [Fi22W.G 0, Fi22W.G 1] = true := by
  quickRfl

theorem gens_eq : [fi22A0P, fi22A1P] = ([Fi22W.G 0, Fi22W.G 1].zip [Fi22W.GI 0, Fi22W.GI 1]).map
    (fun p => (unpack 3510 12 p.1, unpack 3510 12 p.2)) := by
  unfold fi22A0P fi22A1P
  rw [Fi22W.genInv_eq (by decide : (0 : ℕ) < 2), Fi22W.genInv_eq (by decide : (1 : ℕ) < 2),
    Fi22W.gen_eq (by decide : (0 : ℕ) < 2), Fi22W.gen_eq (by decide : (1 : ℕ) < 2)]
  rfl

theorem t_eq : fi22RepP 4 = (unpack 3510 12 (Fi22ExtT.L 25), unpack 3510 12 (Fi22ExtT.L 25)) := by
  change (fi22ExtArr 25, fi22ExtArr 25) = _
  rw [Fi22E2067.ext_eq (by decide : (25 : ℕ) < 185)]

theorem targ_eq : [fi22ChainGen 0, fi22ChainGen 1] = [Fi22W.G 0, Fi22W.G 1].map (unpack 3510 12) := by
  rw [Fi22W.gen_eq (by decide : (0 : ℕ) < 2), Fi22W.gen_eq (by decide : (1 : ℕ) < 2)]
  rfl

end CertificateChecks.KD.LQT.C1037301

end
