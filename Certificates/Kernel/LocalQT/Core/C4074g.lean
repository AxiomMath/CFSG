module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M23Inputs
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import Certificates.Kernel.LocalQT.Core.D4074
public import Certificates.Kernel.LocalQT.Core.D4074s

public section

namespace CFSG.KD.LQT.C4074

open CFSG.KC.LQT.W CFSG.QuasithinUnique.A5.Kc3M23

theorem hGL : [((m23a : _) : Equiv.Perm (Fin 23)), ((m23b : _) : Equiv.Perm (Fin 23)),
    ((m23a⁻¹ : _) : Equiv.Perm (Fin 23)), ((m23b⁻¹ : _) : Equiv.Perm (Fin 23))].map codeP =
      CFSG.KD.LQT.C4074.GL := by
  decide +kernel

theorem hGLs : [((m23a : _) : Equiv.Perm (Fin 23)), ((m23b : _) : Equiv.Perm (Fin 23)),
    ((m23a⁻¹ : _) : Equiv.Perm (Fin 23)), ((m23b⁻¹ : _) : Equiv.Perm (Fin 23))].map codeP =
      CFSG.KD.LQT.C4074s.GL := by
  decide +kernel

end CFSG.KD.LQT.C4074

end
