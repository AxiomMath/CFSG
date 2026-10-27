module

public import CFSG.Certificates.Kernel.LocalQTWordSound
public import Certificates.Kernel.LocalQT.Core.D4078h
public import Certificates.Kernel.LocalQT.Core.D4078d
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.KD.LQT.C4078

open CFSG.KC.LQT.W CFSG.Sporadic.Mathieu

theorem hGLh : [((m22a : _) : Equiv.Perm (Fin 22)), ((m22b : _) : Equiv.Perm (Fin 22)),
    ((m22a⁻¹ : _) : Equiv.Perm (Fin 22)), ((m22b⁻¹ : _) : Equiv.Perm (Fin 22))].map codeP =
      CFSG.KD.LQT.C4078h.GL := by
  decide +kernel

theorem hGLd : [((m22a : _) : Equiv.Perm (Fin 22)), ((m22b : _) : Equiv.Perm (Fin 22)),
    ((m22a⁻¹ : _) : Equiv.Perm (Fin 22)), ((m22b⁻¹ : _) : Equiv.Perm (Fin 22))].map codeP =
      CFSG.KD.LQT.C4078d.GL := by
  decide +kernel

end CFSG.KD.LQT.C4078

end
