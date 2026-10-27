module

public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.TwinPerpSmSp1WitL34
meta import Certificates.Data.TwinPerpSmSp1WitL34
meta import Certificates.Kernel.LocalComp.BfsGen
meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

namespace CertificateChecks.KernelQ8W.L34E

open CFSG.PSL3Four.Native

meta def wL : List Nat :=
  let tabs := (enumBFS 42 gensS 20160).tabs
  let idx : Std.HashMap Nat Nat := (List.range tabs.size).foldl
    (fun m k => m.insert (CFSG.KS.RawGen.pack 6 tabs[k]!) k) {}
  let pts := (CFSG.KC.BfsGen.search 42 6
    (CFSG.CGT.PushingUpLit.SolKNA.R4.Check.qGens Certificates.TwinPerpSmSp1.l34Wit.syl)).1
  pts.toList.map fun a => (idx.get? (CFSG.KS.RawGen.pack 6 (CFSG.KS.RawGen.comp 42 a a))).getD 0

end CertificateChecks.KernelQ8W.L34E

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelQ8W.L34.W include_bytes "data/L34ExtData.W.items" 1416 6790868933677084381

end
