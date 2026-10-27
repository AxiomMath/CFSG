module

public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LocalQT.Steps
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.CFSGNative.SectionRank.Fi24prime

public meta section

namespace CertificateChecks.KernelLC.F24

open CFSG.SectionRank.Native

meta def extOps : List Op :=
  let o := fi24primeData.outs.toArray
  ((List.range 4).flatMap fun i =>
      [Op.mul o[i]! o[i]! (121 + 2 * i), Op.mul (121 + 2 * i) o[i]! (122 + 2 * i)]) ++
    ((List.range 4).flatMap fun i => (List.range i).flatMap fun j =>
      [Op.mul o[i]! o[j]! 0, Op.mul o[j]! o[i]! 0]).zipIdx.map fun (op, t) =>
        match op with
        | .mul a b _ => .mul a b (129 + t)
        | .pow e a _ => .pow e a (129 + t)

meta def fi24Ext : Data :=
  { fi24primeData with nregs := 141, prog := fi24primeData.prog ++ extOps, outs := [] }

end CertificateChecks.KernelLC.F24

end

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LC.F24 CertificateChecks.KernelLC.F24.fi24Ext 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2
