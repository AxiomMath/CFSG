module

public import Certificates.Data.Kernel.L5.Sh0Img
public import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
meta import CFSG.GH74.GLS.C3.Layer2.L5C5cInputs

namespace CFSG.Certificates.Kernel.L5S

open CFSG.GH74.GLS.C3.Layer2.L5

meta def c5067mtA : Array (Array Nat) := #[mt0]

meta def c5067ivA : Array (Array Nat) := #[inv0]

open CFSG.KC.Eval in
meta def c5067wdStep : Step := fun _ =>
  return #[(.anonymous, Val.list (Wd.map fun r => Val.list (r.toArray.map fun x => Val.nat x)))]

end CFSG.Certificates.Kernel.L5S

public section

#kmisc_packarrs CFSG.Certificates.Kernel.L5S.tPT CFSG.Certificates.Kernel.L5S.c5067mtA 7
#kmisc_packarrs CFSG.Certificates.Kernel.L5S.iPT CFSG.Certificates.Kernel.L5S.c5067ivA 7
#kc_eval CFSG.Certificates.Kernel.L5S wL CFSG.Certificates.Kernel.L5S.c5067wdStep

namespace CFSG.Certificates.Kernel.L5S

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5

@[expose] noncomputable def tP (n : Nat) : Nat :=
  if n < 16384 then Nat.land (Nat.shiftRight (tPT 0) (Nat.mul 7 n)) 127 else 0

@[expose] noncomputable def iP (n : Nat) : Nat :=
  if n < 128 then Nat.land (Nat.shiftRight (iPT 0) (Nat.mul 7 n)) 127 else 0

theorem c5067tP_chk : (List.range 16384).all (fun n => tP n == tF n) = true := by decide +kernel

theorem c5067iP_chk : (List.range 128).all (fun n => iP n == iT n) = true := by decide +kernel

theorem c5067wL_chk : (wL == wdK) = true := by decide +kernel

theorem c5067wL_len : wL.length = 128 := by decide +kernel

@[expose] noncomputable def c5067clsI (c : Nat) : Bool :=
  (invLT tP).all fun x0 => !(x0 / 11 == c) ||
    classifyRowI tP iP gsK wL relK RIdxC (invLT tP) 32 xsK ssK x0

end CFSG.Certificates.Kernel.L5S

end
