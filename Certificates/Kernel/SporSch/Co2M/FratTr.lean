
module

public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Sporadic.Co2Schreier.SylowCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.SylowCheckInputs
public meta import Certificates.Kernel.SporSch.Co2M.EnumGen
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Co2M.EnumGen
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelSporSch.Co2M.FratData

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CertificateChecks.KernelSporSch.Co2M.Gen
open CFSG.Monster.B.Co2.Native

meta def bas : Array (List Nat) := basisOf co2PackedVecs

meta def lvF : Array Level := fratLevels

meta def trMats (i c : Nat) (inv : Bool) : List Nat :=
  (List.range c).map fun k =>
    matOf co2PackedVecs bas (if inv then lvF[i]!.trInv[k]! else lvF[i]!.tr[k]!)

meta def t0 : List Nat := trMats 0 128 false
meta def t0i : List Nat := trMats 0 128 true
meta def t1 : List Nat := trMats 1 64 false
meta def t1i : List Nat := trMats 1 64 true

meta def yz : List Nat :=
  (List.range 32).map (fun w => matOf co2PackedVecs bas (yArr w)) ++ [matOf co2PackedVecs bas zArr]

meta def ys : Array (Array Nat) :=
  (Array.range 32).map yArr ++ (Array.range 32).map fun w => invCand 2300 (yArr w)

end CertificateChecks.KernelSporSch.Co2M.FratData

#knatlist CertificateChecks.KernelSporSch.Co2M.FT0 CertificateChecks.KernelSporSch.Co2M.FratData.t0
#knatlist CertificateChecks.KernelSporSch.Co2M.FT0I CertificateChecks.KernelSporSch.Co2M.FratData.t0i
#knatlist CertificateChecks.KernelSporSch.Co2M.FT1 CertificateChecks.KernelSporSch.Co2M.FratData.t1
#knatlist CertificateChecks.KernelSporSch.Co2M.FT1I CertificateChecks.KernelSporSch.Co2M.FratData.t1i
#knatlist CertificateChecks.KernelSporSch.Co2M.FYZ CertificateChecks.KernelSporSch.Co2M.FratData.yz
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.FY CertificateChecks.KernelSporSch.Co2M.FratData.ys 12
