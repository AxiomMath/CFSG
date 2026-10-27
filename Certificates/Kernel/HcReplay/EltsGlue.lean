module

public import Certificates.Kernel.HcReplay.Elts
public import CFSG.Certificates.Kernel.HcReplaySound
public import CFSG.Certificates.Kernel.HcPackSound
import all Certificates.Data.Kernel.HcPack
import all Certificates.Data.G23RecogGlueInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23

theorem gensL_map_pk : gensL.map pk = hcG := by decide +kernel

theorem idP_eq : idP = 1459980823972598128486511383358617792788444579872 := by decide +kernel

theorem bfsP_hcG : bfsP hcG = hcElts.E := by
  rw [bfsP, idP_eq]
  exact bfsAux_of_replayB _ _ _ _ _ _ _ _ hcElts_replay

theorem elts_map_pk_eq : elts.map pk = hcElts.E := by
  rw [elts_map_pk, gensL_map_pk, bfsP_hcG]

end CFSG.KC.HcPack

end
