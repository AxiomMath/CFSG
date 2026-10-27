module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
import Certificates.Kernel.LocalComp.SurjGen
meta import Certificates.Data.CFSGNative.Bridge.Fi23GPL

public section

#ks_chars CFSG.KD.BrFi23.IT CFSG.Sporadic.Bridge.Fi23GPL.Native.imgText
#ks_chars CFSG.KD.BrFi23.ST CFSG.Sporadic.Bridge.Fi23GPL.Native.surjText
#lc_words CFSG.KD.BrFi23.IT CFSG.Sporadic.Bridge.Fi23GPL.Native.imgText
#lc_words CFSG.KD.BrFi23.ST CFSG.Sporadic.Bridge.Fi23GPL.Native.surjText

namespace CFSG.KD.BrFi23

@[expose] noncomputable def seedL (z : Int) : Nat × Bool :=
  if z = 1 then (10, true) else if z = -1 then (10, false) else if z = 2 then (11, true)
  else (11, false)

@[expose] noncomputable def imgL (z : Int) : Nat × Bool :=
  if 0 < z then ((z - 1).toNat, true) else ((-z - 1).toNat, false)

@[expose] noncomputable def relsX : List (List (Nat × Bool)) :=
  CFSG.Sporadic.Bridge.Fi23GPL.Native.rels () ++
    (IT.W.zipIdx.map fun (w, k) => w.map seedL ++ [(k, false)]) ++
    (ST.W.zipIdx.map fun (w, i) => w.map imgL ++ [(10 + i, false)])

end CFSG.KD.BrFi23

end
