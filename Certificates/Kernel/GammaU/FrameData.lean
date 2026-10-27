module

public import Certificates.Kernel.GammaU.CensusCfgData
public import Certificates.Kernel.GammaU.Census0Data
public import Certificates.Data.Kernel.GammaUFrameK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUF "Certificates/Kernel/GammaU/data/frame.json.gz" 847
  1279642578073916008 (SA : List Nat) (SAI : List Nat) (SJ : List Nat)

namespace CFSG.KD.GUF

open CFSG.KC.IF4C CFSG.KC.GUV

@[expose] noncomputable def D0F : List Nat := [961, 48, 9, 5, 3, 3072]

@[expose] noncomputable def cgOK : Bool :=
  allBelow 160 fun k => guOK CFSG.KD.GUC0.TH (look CFSG.KD.GUC0.CG k)

@[expose] noncomputable def dtsOK : Bool :=
  allBelow 108 fun j => dtOK CFSG.KD.GUC0.TH (look CFSG.KD.GUCC.DT j)

@[expose] noncomputable def teOK : Bool :=
  allBelow CFSG.KD.GUCC.NE fun n => guOK CFSG.KD.GUC0.TH (look CFSG.KD.GUCC.TE n)

@[expose] noncomputable def sjOK (s : Nat) : Bool :=
  allBelow 108 fun j => Nat.blt (nthD 0 SJ (Nat.add (Nat.mul 108 s) j)) 108 &&
    sjAt D0F (nthD 0 SA s) (nthD 0 SAI s) (look CFSG.KD.GUCC.DT j)
      (look CFSG.KD.GUCC.DT (nthD 0 SJ (Nat.add (Nat.mul 108 s) j)))

@[expose] noncomputable def saOK : Bool :=
  Nat.beq (lenN SA) 2 && Nat.beq (lenN SAI) 2 &&
    allBelow 2 fun s => Nat.beq (mulP (nthD 0 SA s) (nthD 0 SAI s)) idP

end CFSG.KD.GUF

end
