
module

public import Certificates.Kernel.SporSch.Co2M.FratMD
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import Certificates.Kernel.SporSch.Co2M.EnumGen
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Co2M.EnumGen
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native

meta def thVecsM : Array Nat := co2PackedVecs

meta def thGRows : Array (Array Nat) :=
  ((oddMats witRec).map fun rows => transposeRows 22 rows.toArray).toArray

meta def thGIRows : Array (Array Nat) :=
  (gArrsOf co2PosTable witRec).map fun a =>
    Gen.rowsOf (Gen.matOf thVecsM (Gen.basisOf thVecsM) (CFSG.Monster.B.Co2.Native.invCand 2300 a))

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.TGM CertificateChecks.KernelSporSch.Co2M.thGRows 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.TGMI CertificateChecks.KernelSporSch.Co2M.thGIRows 22

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KS.Co2M CFSG.Sporadic.Co2Schreier

@[expose] noncomputable def teGT : List (ℕ × ℕ) := (List.range 15).map fun j => (TGM j, TGMI j)

@[expose] noncomputable def tePow (p : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (I22, I22)
  | e + 1 => cmpP (tePow p e) p

@[expose] noncomputable def teQT : List (ℕ × ℕ) :=
  quRecipe.map fun r => tePow (prodPT teGT r.1) r.2

@[expose] noncomputable def teU : ℕ × ℕ := cmpP (sT.getD 8 (0, 0)) (sT.getD 0 (0, 0))

end CertificateChecks.KernelSporSch.Co2M

end
